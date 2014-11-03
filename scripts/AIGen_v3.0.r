# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# ========================================================================
# ========================================================================
# Copyright 2014 University of Melbourne
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
# ========================================================================
# ========================================================================
#
# Purpose: the algorithm is developed to measure the urbanization 
#          index of different countries using CIESIN grid data: http://sedac.ciesin.columbia.edu/data/set/gpw-v3-population-density/data-download 
# Version: 3.0
# Last Updated: 14-Aug-2014
# Written by: Dr. Yiqun Chen    yiqun.c@unimelb.edu.au
#             Dr. Jennifer Day    jday@unimelb.edu.au
#  
# Data Preparation Process
# Here is a recommended processing flow to convert and combine CIESIN population grid and density grid from raster to vector (point) for the algorithm
#  (1) load the grid raster(e.g. pakds00ag, population densities in 2000, adjusted to match UN totals, persons per square km) into ArcGIS
#  (2) in ArcToolbox, choose "Coversion Tools" -> "From Raster" -> "Raster to Point", save output shp file as "pakds00ag.shp"
#  (3) load the grid raster(e.g. pakp00ag, population counts in 2000, adjusted to match UN totals) into ArcGIS
#  (4) in ArcToolbox, choose "Coversion Tools" -> "From Raster" -> "Raster to Point", save output shp file as "pakp00ag.shp"
#  (5) in ArcToolbox, choose "Analysis Tools" -> "Overlay" -> "Spatial Join", choose "pakds00ag.shp" as target features and "pakp00ag.shp" as join features, save output shp file as "pak00ag.shp", match option is "Intersect" and leave the rest setting as defaults. 
#  (6) save a copy of the output "pak00ag.dbf" file, 
#  (7) load "pak00ag.dbf" in SPSS, in variable view, rename column "*grid_code" as "DEN" and "*grid_code_" as "POP", keep column "pointid" and delete all rest columns. save it with the same name and in "dBASE IV (*.dbf)" format.
#  (8) load "pak00ag.shp" in ArcGIS and double check the result.
#  (9) done.
#
# Change Log:
# (v3.0) (1)add "equationType" parameter to choose the equation for  grid-seed merging process 
#        ATTENTION: different equationType options may generate different grid-seed pair candidates, 
#                   and since there is no guarantee that each combination of grid-seed pair will eventually form an agglomeration, so the final result may vary based on different equationType options
#        (2) when seedMergeMethod is set to "exingravity", the algorithm will take into account the distance threshold as well. 
#           it calculates the shortest euclidian distance of two grids that belongs to two seeds repectively, and then compares it with a threshold value (60km) to determine if these two seeds are mergeable or not
#		 (3) adding license stuff 
# (v2.6) (1)add a new processing control varialbe: gLoopStartIndex, defualt as 1
#        In case of the process ends abnornally, e.g. experiencing network exceptions, or being terminated by ourselves since it's time to go home, 
#        and later we wanna continue the processing instead of starting for the every beginning again, we can set this variable with the 'index value' showing in the last output line:
#        [1088/14012]=====gridId: 2340
#        [index value / total grid number]=====gridId: grid Id
#        In this example, we need to set gLoopStartIndex to 1088.
#        ATTENTION: make sure to set gUseCachedRouteDBOnly to FALSE to avoid missing route info from real API calls if a 'complete' cached DB is not constructed yet.
#
#        (2)add a new processing control variable: gUseCachedRouteDBOnly, default as FALSE
#        This is a time-saving option. ALWAYS set it to FALSE  for the first run if any changes in seed or grid data sources.
#        If set to TRUE, it only queries the route info from cached DB and won't call APIs even it cannot find the route from DB. It works great for two scenarios:
#        (a) With the seed and grid datasource unchanged, if we start the first run with a loose set of configurations such as (150:50000:60) and the entire process ends normally,
#           then we will have a 'complete' cached route DB fully covers all routes for a harsh set of configurations such as (150:100000:60) or (300:50000:60) or (300:100000:60) or (150:50000:30).
#           so if we plan to run it again over these configurations, we can safely set gUseCachedRouteDBOnly to TRUE. 
#        (b) In same extreme cases, for example, when processing grids for Indea, the data set is too big to be handled properly in one run (it could be, but very likely to be terminated by network errors due to the long processing time). 
#           but we eventually can work out a 'complete' cached route DB part by part using gLoopStartIndex variable. Since the process is interrupted, we have to run it again to genereate AI values (ATTENTION: gLoopStartIndex must set to 1).
#           Because the cached DB is complete , we can set gUseCachedRouteDBOnly to FALSE to accelerate the process. 
#
# (v2.5) new auto-save feature, it periodically saves api route query data to local disk to aviod data loss when process is terminated abnormally. 
# (v2.4) merge two methods into a single function
# (v2.3) change how internal gravity for seed is calculated  so that it is in line with univisal gravitation equation:
#       suppose there is two seeds s and s', where pop(s) > pop(s') and there are n grids (gi where 1<=i<=n) surrounding s'.
#       to decide whether s' should be merged to s or keep its independence with its gi, we need to compute its external univisal gravitation force with s and 
#       internal univisal gravitation force with all gi:
#
#       (E1) exG = G*pop(s)*pop(s')/(dist(s,s')^2)
#       (E2) inG = sum(G*pop(gi)*pop(s')/(dist(gi,s')^2))
#       where 1<=i<=n and G is a constant
#
#       if exG > inG, then s' will be merged to s
#       if exG <= inG, then s' stays independent.
#
#       TO compare the values of E1 and E2, the equation can be simplied as:
#       (E3) exG = pop(s)/(dist(s,s')^2)
#       (E4) inG = sum(pop(gi)/(dist(gi,s')^2))
#       where 1<=i<=n
#
#       The next question is how to define a 'boundary' to include all necessary gi for E4, in other words, what gi is qualified to participate E4
#       The solution is to choose grids from those which are aggregated to s'. 
#       An additional distance threshold is also applied to exclude grids which are too close to s' geographically, because they can blow up the inG easily. 
#       To some extent, if grids are too close to seed, they can be treated as the seed or part of the seed. Hence, it is reasonable to exclude them.
#       The distance threshold is set to the length of grid edge. For Srilanka grid dataset, it is 4.5KM
#     
# (v2.2) modify the gravity equation(give user chance to change)
# (v2.2) add srsDF to host all interested country's projection srs
# (v2.2) add two method for seed agglomeration: (1) minimaldist (2)ex-in gravity 
# (v2.1) add new method "f_genAI_2" to support agglermoration from single grid file (seeds are selected from grids on condition)
# (v2.0) asking for particular project crs, if it cannot be provided, use the univisal one (EPSG:3857), 
# 
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # 

# required packages
library(maptools)   # for geospatial services; also loads foreign and sp
library(rgdal)      # for map projection work; also loads sp
library(rgeos)
library(RCurl)
library(rjson)
library(RecordLinkage)

# set up the working directory
setwd("/Users/yiqunc/githubRepositories/gridaa")

# the outputs for a country in a specific year will be stored at "gOutRootDirgCountryName/gDataYear/seedDirName" 
gOutRootDir <<- "./output/"
gCountryName <<- "SriLanka"
gDataYear <<- "2000"

# if travel distance / euclidean distance is bigger than gTERMax, the API results are treated as issused ones and need further correction.
gTERMax <<- 3.0

# global dataframe to store RouteInfo
gRouteInfoDF = NULL

# global auto routeinfo save threshold, e.g., every 200 new routes are obtained from API, save them locally 
gRouteInfoAutoSaveNum = 200

# only try to find route info from cached DB, won't call API again. 
# ATTENTION: always set gUseCachedRouteDBOnly to FALSE for the first run and don't turn it to TRUE until you read change log v2.6 carefully
gUseCachedRouteDBOnly = FALSE

# the start index of processing loop, default as 1
gLoopStartIndex = 1

# show debug infomation when processing
gShowDebugInfo = TRUE

# define URL templates
MapQuestKeyString = "&key=Fmjtd%7Cluua25uzl9%2Cbn%3Do5-962suy"
MapQuestDirectURLTemplate = "http://open.mapquestapi.com/directions/v1/route?outFormat=json&from=%.6f,%.6f&to=%.6f,%.6f&routeType=fastest&narrativeType=none&generalize=0&doReverseGeocode=false&unit=k"
GoogleDirectURLTemplate = "http://maps.googleapis.com/maps/api/directions/json?origin=%.6f,%.6f&destination=%.6f,%.6f&sensor=false"
GoogleGeoCodingURLTemplate = "http://maps.googleapis.com/maps/api/geocode/json?latlng=%.6f,%.6f&sensor=false"

# define SRS for case study area, use the "Proj4js format" string declared in http://spatialreference.org/ 
# Finding a proper projected srs is important for accurate projection. It affects the result of euclidean distance calculation.
#using EPSG:3857 for universal projected crs http://trac.osgeo.org/proj/wiki/FAQ. This is NOT the best solution for any particular area.
CONST_projected_proj4string_universal = "+proj=merc +a=6378137 +b=6378137 +lat_ts=0.0 +lon_0=0.0 +x_0=0.0 +y_0=0 +k=1.0 +units=m +nadgrids=@null +wktext +no_defs" #"+proj=merc +datum=WGS84"

srsDF = data.frame(countryname=NULL, EPSG=NULL, proj4string=NULL)
# SLD99 / Sri Lanka Grid 1999: https://code.google.com/p/pyproj/source/browse/trunk/lib/pyproj/data/epsg?r=286
srsDF <<- rbind(srsDF,data.frame(countryname="SriLanka", EPSG="", proj4string="+proj=tmerc +lat_0=7.000471527777778 +lon_0=80.77171308333334 +k=0.9999238418 +x_0=500000 +y_0=500000 +a=6377276.345 +b=6356075.41314024 +towgs84=-0.293,766.95,87.713,0.195704,1.69507,3.47302,-0.039338 +units=m +no_defs") )
srsDF <<- rbind(srsDF,data.frame(countryname="Bangladesh", EPSG="EPSG:3106", proj4string="+proj=tmerc +lat_0=0 +lon_0=90 +k=0.9996 +x_0=500000 +y_0=0 +a=6377276.345 +b=6356075.41314024 +units=m +no_defs") )
srsDF <<- rbind(srsDF,data.frame(countryname="Nepal", EPSG="", proj4string="+proj=tmerc +lat_0=0 +lon_0=84 +k=0.9999 +x_0=500000 +y_0=0 +a=6377276.345 +b=6356075.41314024 +units=m +no_defs") )
srsDF <<- rbind(srsDF,data.frame(countryname="Bhutan", EPSG="EPSG:5266", proj4string="+proj=tmerc +lat_0=0 +lon_0=90 +k=1 +x_0=250000 +y_0=0 +ellps=GRS80 +towgs84=0,0,0,0,0,0,0 +units=m +no_defs") )


CONST_projected_proj4string = as.vector(srsDF[srsDF[,"countryname"] == gCountryName,"proj4string"])

if(length(CONST_projected_proj4string)==0 || CONST_projected_proj4string == ""){
  CONST_projected_proj4string = CONST_projected_proj4string_universal
}
  
#using EPSG:4326 for unprojected crs
CONST_unprojected_proj4string = "+proj=longlat +ellps=GRS80 +towgs84=0,0,0,0,0,0,0 +no_defs"
#define epsg string, which correct the ".prj" file creation issue in 
CONST_unprojected_proj4string_epsg = "+init=epsg:4326"

debugPrint <- function(str){
  if(gShowDebugInfo){
    print(str)
  }
}

# load route info from file
RouteInfo.load <- function(filePath){
  if (file.exists(filePath)){
    con <- file(filePath, open="r") 
    gRouteInfoDF <<- read.table(con, header=TRUE, sep=",", blank.lines.skip = TRUE, fill = TRUE)
    close(con)
  } else {
    gRouteInfoDF <<- data.frame(startIdx=NULL, endIdx=NULL, eucDist=NULL, tvlDist=NULL, tvlTime=NULL, api=NULL, jsonPath=NULL)
  }
}

# append new route into gRouteInfoDF
RouteInfo.append <- function(startIdx=0, endIdx=0, eucDist=0, tvlDist=0, tvlTime=0, api="MQ", jsonPath="", routeInfoFilePath=""){
  gRouteInfoDF <<- rbind(gRouteInfoDF,data.frame(startIdx=startIdx, endIdx=endIdx, eucDist=eucDist, tvlDist=tvlDist, tvlTime=tvlTime, api=api, jsonPath=jsonPath))

  # triger auto save if increment meets the condition 
  if (!is.null(nrow(gRouteInfoDF))){
    if (nrow(gRouteInfoDF) %% gRouteInfoAutoSaveNum == 0){
      RouteInfo.save(routeInfoFilePath)
      debugPrint(sprintf("====================== auto-save at [%i] routes",nrow(gRouteInfoDF)))
    }
  }
}

# query route info from gRouteInfoDF based in start and end index
RouteInfo.query <- function(startIdx=0, endIdx=0){
  rlt = NULL
  if (!is.null(nrow(gRouteInfoDF))){
    if (nrow(gRouteInfoDF) > 0){
      sFilter = gRouteInfoDF[,"startIdx"] == startIdx
      eFilter = gRouteInfoDF[,"endIdx"] == endIdx
      rlt = gRouteInfoDF[sFilter&eFilter,]
    }
  }
  return(rlt)
}

# save route info into file
RouteInfo.save <- function(filePath){
  con <- file(filePath, open="w")
  write.table(gRouteInfoDF, file=filePath, row.names = FALSE, sep=",")
  close(con)
}

# generate centroids inside polygons
InnerCentroids.gen <- function(pols, trynum=10, accurate=TRUE) {
  # # # # # # # # # # # # # # # # # # # # # # # # # # # #
  # find inner centroid for polygons using negative buffer
  # inspired by http://r-sig-geo.2731867.n2.nabble.com/Better-label-placement-for-polygons-td7580550.html
  # Input:
  # (1) pols: SpatialPolygonsDataFrame
  # (2) trynum: how many times algorithm can try to neg-buffer. Once trynum is reached, the default gCentroid result will be used, it means an inner centroid is nor found.
  # (3) accurate: if false, in each neg-buffer loop, the centroid of new polygon will be tested to see if it is within the original polgyon; 
  #               if true, in each neg-buffer loop, the centroid of new polygon will be tested to see if it is within the new polgyon;
  # Output:
  # a list of centroids, each element is SpatialPoints
  # # # # # # # # # # # # # # # # # # # # # # # # # # # #
  
  #plot(pols)
  centroidList = list()
  # For each polygon in pols, calculate the appropriate label point 
  for(i in seq_len(length(pols))) { 
    debugPrint(sprintf("=== calc inner centroid for polygon[%i]",i))
    p = pols[i,]
    
    # fill the centroidList with default centroid
    centroidList[[i]] = gCentroid(p)
    
    # continue if the centroid is already within polygon
    if (gWithin(centroidList[[i]], p)){
      #plot(centroidList[[i]], col="green", add=TRUE)
      next
    }
    
    # init buffer distance
    radius = sqrt(gArea(p)/pi)
    r = radius
    maxr = radius
    minr = 0
    counter = 0
    
    # try to find the inner centroid
    repeat {
      # exit condition test
      if (counter > trynum) break
      
      # shrink and create a new polygon
      p2 = gBuffer(p, width = -r)
      
      # if r is too big, the new polygon will be empty, try to decrease r
      if (gArea(p2) <= 0){
        maxr = r
        r = r - (maxr-minr)/2
        #debugPrint(sprintf("===keep going r:%.8f, step:%.8f",r,estep))
      } else {
        # if new polygon is not empty, let's test if its centroid is good enough to use
        centroid = gCentroid(p2)
        if (accurate == TRUE){
          flag = gWithin(centroid, p2)
        } else {
          flag = gWithin(centroid, p)
        }
        # if centroid is within polygon (new or original), we take it
        if (flag){
          centroidList[[i]] = centroid
          #debugPrint(centroid)
          #plot(centroidList[[i]], col="red", add=TRUE)
          break
        } else {
          # if not, it means the new polygon is not bufferred (or smooth) enough to hold its centroid inside, try to increase r
          minr = r
          r = r + (maxr-minr)/2
          #debugPrint(sprintf("not within===keep going r:%.8f, step:%.8f",r,estep))
        }
      }
      counter = counter + 1
    } 
  }
  
  # return the result
  return(centroidList)
}

# load centroids
InnerCentroids.load <- function(filePath, pols, trynum=10, accurate=TRUE) {
  centroidList = list()
  if (file.exists(filePath)){
    original_proj4string = attr(pols@proj4string,"projargs")
    con <- file(filePath, open="r")
    coordsDF = read.table(con, header=TRUE, sep=",", blank.lines.skip = TRUE, fill = TRUE)
    close(con)
    
    for (i in 1:nrow(coordsDF)){
      centroidList[[i]] = SpatialPoints(list(coordsDF[i,"x"], coordsDF[i,"y"]), proj4string=CRS(original_proj4string))
    }

    debugPrint("++++++++++++++++ cached centroids applied ++++++++++++++++++++")
  } else {
    centroidList = InnerCentroids.gen(pols,trynum,accurate)
    #save centroid
    InnerCentroids.save(filePath, centroidList)
  }
  
  #return centroids
  return(centroidList)
}

# save centroids locally
InnerCentroids.save <- function(filePath, ctrdList){
  coordsDF = data.frame(x=NULL, y=NULL)
  for (i in 1:length(ctrdList)){
    lat = ctrdList[[i]]@coords[2]
    lon = ctrdList[[i]]@coords[1]
    coordsDF <- rbind(coordsDF,  data.frame(x=lon, y=lat))
  }
  con <- file(filePath, open="w")
  write.table(coordsDF, file=filePath, row.names = FALSE, sep=",")
  close(con)
  debugPrint("++++++++++++ centroids are cached ++++++++++++")
}

# get the distance between two latlon location
GeoTool.getLatLonDistance <- function(sLat, sLon, eLat, eLon){
  
  s_lon = c(sLon)
  s_lat = c(sLat)
  s = SpatialPoints(list(s_lon, s_lat),proj4string=CRS(CONST_unprojected_proj4string))
  s_pj = spTransform(s,CRS(CONST_projected_proj4string))
  e_lon = c(eLon)
  e_lat = c(eLat)
  e = SpatialPoints(list(e_lon, e_lat),proj4string=CRS(CONST_unprojected_proj4string))
  e_pj = spTransform(e,CRS(CONST_projected_proj4string))
  # return projected distance in meters
  return(gDistance(s_pj, e_pj))
}

# convert csv file (with lat-lon columns) to shp file
# todo: extend to support all epsg codes
GeoTool.csv2shp <- function(dsn = "./data/srilanka/",
                                    targetShpFileName="CESIN_cities_Sri_Lanka_v3",
                                    sourceCSVFilePath = "./data/srilanka/CESIN_cities_Sri_Lanka_v3.csv"
){
  dataDF = read.csv(file = sourceCSVFilePath, header=TRUE, sep=",")
  #this will generate a problemetic prj file
  #dataSPDF = SpatialPointsDataFrame(dataDF[,c("Long","Lat")], dataDF, proj4string=CRS(CONST_unprojected_proj4string))
  #this will generate a correct prj file
  dataSPDF = SpatialPointsDataFrame(dataDF[,c("Long","Lat")], dataDF, proj4string=CRS("+init=epsg:4326"))
  writeOGR(obj=dataSPDF, dsn=dsn, layer=targetShpFileName, driver="ESRI Shapefile", check_exists=TRUE, overwrite_layer=TRUE)  
  
}

# a generic gravity equation generator, by default it uses "SQUAREDDIST" equation. 
GeoTool.getGravity <- function(massPara, distPara, equationType="SQUAREDDIST"){
  if(equationType == "SQUAREDDIST"){
    if(distPara < 0.0000001) {
      return (999999999.0)
    } else {
      return (massPara/(distPara^2))
    }
  }
  if(equationType == "SINGLEDIST"){
    if(distPara < 0.0000001) {
      return (999999999.0)
    } else {
      return (massPara/distPara)
    }
  }
  if(equationType == "DISTONLY"){
    if(distPara < 0.0000001) {
      return (999999999.0)
    } else {
      return (1/distPara)
    }
  }
  if(equationType == "USERDEFINED"){
    # users have to define the equation by themselves
    return(999999999.0)
  }
}

# ATTENTION: if additional seed file is NOT provided, the seed will directly be selected from population grids, which generally contain smaller population values than provided by the seed file. Make sure to adjust 'ThSeedMinPop' to fit different options
AI.gen <- function(dsn = "./data/srilanka/", 
                   gridFileName = "lkadensp00ag", 
                   seedFileName = "CESIN_cities_Sri_Lanka_v3",
                   gridDenColName = "DEN",
                   gridPopColName = "POP",
                   seedPopColName = "pop2001",
                   seedNameColName = "city_name",
                   outDir = gOutRootDir,
                   thPopDen = 150, 
                   thSeedMinPop = 100000, 
                   thTvlTime = 60, 
                   thSearchSeedRadius = 80, 
                   thGeoCodingDistShift = 1,
                   seedAsTopNHighPopArea = -1,
                   seedDirName = "ByTopPop",
                   countryName = gCountryName,
                   dataYear = gDataYear,
                   seedMergeDist = 60,
                   seedMergeTo = "highestPop",
                   seedMergeMethod = "exingravity",
                   gridEdgeLength = 4.5,
                   equationType = "SQUAREDDIST"
                   )
{
  # use a separate seed file 
  if(seedFileName != ""){
    f_genAI(dsn = dsn, 
            gridFileName = gridFileName, 
            seedFileName = seedFileName,
            gridDenColName = gridDenColName,
            gridPopColName = gridPopColName,
            seedPopColName = seedPopColName,
            seedNameColName = seedNameColName,
            outDir = outDir,
            thPopDen = thPopDen, 
            thSeedMinPop = thSeedMinPop, 
            thTvlTime = thTvlTime, 
            thSearchSeedRadius = thSearchSeedRadius, 
            thGeoCodingDistShift = thGeoCodingDistShift,
            seedDirName = seedDirName,
            countryName = countryName,
            dataYear = dataYear,
            seedMergeDist = seedMergeDist,
            seedMergeTo = seedMergeTo,
            seedMergeMethod = seedMergeMethod,
            gridEdgeLength = gridEdgeLength,
            equationType = equationType
      )
  }else{
  # extract seed from grid file
    f_genAI_2(dsn = dsn, 
              gridFileName = gridFileName, 
              gridDenColName = gridDenColName,
              gridPopColName = gridPopColName,
              outDir = outDir,
              thPopDen = thPopDen, 
              thSeedMinPop = thSeedMinPop, 
              thTvlTime = thTvlTime, 
              thSearchSeedRadius = thSearchSeedRadius, 
              thGeoCodingDistShift = thGeoCodingDistShift,
              seedAsTopNHighPopArea = seedAsTopNHighPopArea, 
              seedDirName = seedDirName,
              countryName = countryName,
              dataYear = dataYear,
              seedMergeDist = seedMergeDist,
              seedMergeTo = seedMergeTo,
              seedMergeMethod = seedMergeMethod,
              gridEdgeLength = gridEdgeLength,
              equationType = equationType
              )
  }
  
}

# generate Agglomeration Index based on separate grid and seed files
f_genAI <- function(dsn="./data/srilanka/", 
                    gridFileName="lkadensp00ag", 
                    seedFileName="lkapv1",
                    gridDenColName = "DEN",
                    gridPopColName = "POP",
                    seedPopColName = "ES00POP",
                    seedNameColName = "NAME1",
                    outDir=gOutRootDir,
                    thPopDen=150, 
                    thSeedMinPop=100000, 
                    thTvlTime=60, 
                    thSearchSeedRadius=80, 
                    thGeoCodingDistShift=1,
                    seedDirName="ByTopPop",
                    countryName=gCountryName,
                    dataYear=gDataYear,
                    seedMergeDist=60,
                    seedMergeTo="highestPop",
                    seedMergeMethod="exingravity",
                    gridEdgeLength = 4.5,
                    equationType = "SQUAREDDIST"
                    ){
  # # # # # # # # # # # # # # # # # # # # # # # # # # # #
  # Input parameters:
  # (1) dsn: the root directory of data sets
  # (2) gridFileName: grid data (points in shp file) file name.
  # (3) seedFileName: seed data (points in shp file) file name.
  # (4) gridDenColName: population density column name in the grid shp file
  # (5) gridPopColName: population column name in the grid shp file
  # (6) seedPopColName: population column name in the seed shp file
  # (7) outDir: the root directory of calculation outputs
  # (8) thPopDen: threshold of population density. A non-seed area (a grid cell) is only considered as agglomeratable if its popden is bigger than this threshold. unit: the number of people in 1 square km
  # (9) thSeedMinPop: threshold of population. A seed area is only considered and used as an agglomeration core if its population is larger than this threshold. 
  # (10) thTvlTime: threshold of travel time between seed and non-seed districts. unit: minute
  # (11) thSearchSeedRadius: threshold of the Euclidian distance between a non-seed and its potential seeds. Those too distant seeds will be excluded from gravity calculation.
  # (12) thGeoCodingDistShift: threshold of the Euclidian distance between the original point and reverse geocoding point. If the reverse geocoding point is too distant away from the original one, it will not be used.
  # (13) seedDirName: for different seed selections, the result will be put into different output directories This is the directory name for a particular seed selection. It can be any valid and meaningful folder name, no whitespace in it.
  # (14) countryName: the name of the country. It is used as a part of the outputs path
  # (15) dataYear: the year of population data.  It is used as a part of the outputs path
  # (16) seedMergeDist: distance threshold for seeds merge (Unit: km). This parameter will be ignored if seedMergeMethod is set to "exingravity"
  # (17) seedMergeTo: "bboxCentre": among all mergeable seeds, find one who is closeast to thire bbox centre. All other seeds will be aggragated to this 'central seed'
  #                   "highestPop"(default): all mergeable seeds will be merged to the seed whose population is the highest; 
  # (18) seedMergeMethod: if set to "minimaldist", two closest seeds will be merged if their distance is within the seedMergeDist; 
  #                       if set to "exingravity", and if a seed's internal gravity is bigger than its external gravity, it remains independent; 
  # (19) gridEdgeLength: unit (km), the length of grid cell edge. Vary on different grid dataset. For Srilanka, it is 4.5km
  # Output:
  # (1) shp files containing agglomeration index information
  # (2) a calculated route data folder ("routeinfo") containing raw route request api results
  # (3) a calculated inner centroid data file ("innerCentroids.csv") 
  # (4) two AI tables for original seed ("AI_XX_XX_XX_orgseed.csv") and aggregated seed ("AI_XX_XX_XX_aggseed.csv")
  # # # # # # # # # # # # # # # # # # # # # # # # # # # #

algStartTime = Sys.time()
  
# create a folder to hold route information 
routeInfoDir = sprintf("%s%s/genAI/%s/",outDir,countryName,"routeinfo")
dir.create(routeInfoDir, showWarnings=FALSE, recursive=TRUE)
routeInfoFilePath = sprintf("%s%s",routeInfoDir,"db.csv")

# load route info into gRouteInfoDF
RouteInfo.load(routeInfoFilePath)

# create a folder to AI results (shp files) for different seed choices
outShpFileDir = sprintf("%s%s/genAI/%s/%s",outDir, countryName, dataYear, seedDirName)
dir.create(outShpFileDir, showWarnings=FALSE, recursive=TRUE)

# set TRUE to enable seeds agglomeration 
isSeedAgglomeratable = TRUE

# define thresholds 
# POP DENSITY: run an AI at each of these minimum levels: 150, 300, and 500 people per square kilometre
# TRAVEL TIME: run an AI at each of these maximum levels: 30, 60, and 90 minutes
# MINIMUM SEED POPULATION: run an AI at each of these minimum levels: 20,000, 50,000, 100,000, and 500,000.
th_popden = thPopDen
th_tvltime = thTvlTime*60
th_seed_minpop = thSeedMinPop # the minimum population to be considered as a seed

# Eclidian distance to search seeds around a non-seed. Unit: meter. It is used first to reduce real distance computation
th_dist = thSearchSeedRadius*1000
# the maximum Euclidian distance between an orginal point and its reverse geocoding point, if the distance bigger than this threshold, the reverse geocoding point will not be used
th_geocoding_dist_shift = thGeoCodingDistShift*1000 

# load grids
gridRaw <- readOGR(dsn=dsn,layer=gridFileName,encoding="utf8", verbose=FALSE)
# create a gridId column
gridRaw@data[,"gridId"] = c(1:nrow(gridRaw@data))
# add additional columns : aggidx (default 0), aggidx2 (default 0, when seed agglomeration applied) 
gridRaw@data[,"aggidx"] = 0
gridRaw@data[,"aggidx2"] = 0
# if population or density field is null, set it to 0
if(length(which(is.na(gridRaw@data[, gridDenColName])))>0){
  gridRaw@data[which(is.na(gridRaw@data[, gridDenColName])), gridDenColName] = 0
}
if(length(which(is.na(gridRaw@data[, gridPopColName])))>0){
  gridRaw@data[which(is.na(gridRaw@data[, gridPopColName])), gridPopColName] = 0
}

if (is.projected(gridRaw)){
  gridPrj = gridRaw
  gridUnprj = spTransform(gridRaw,CRS(CONST_unprojected_proj4string))
} else {
  gridUnprj = gridRaw
  gridPrj = spTransform(gridRaw,CRS(CONST_projected_proj4string))
}

gridDenFilter = gridUnprj@data[, gridDenColName] >= th_popden

# directly convert from S4 object to keep coords in DF
gridDF = data.frame(gridUnprj[gridDenFilter,])
# extract prj and unprj coords for use
gridCoords_pj = data.frame(gridPrj)[, c("coords.x1","coords.x2")]
gridCoords_unpj = data.frame(gridUnprj)[, c("coords.x1","coords.x2")]


# load seed
seedRaw <- readOGR(dsn=dsn,layer=seedFileName,encoding="utf8", verbose=FALSE)
# create a seedId column
seedRaw@data[,"seedId"] = c(1:nrow(seedRaw@data))
seedRaw@data[,"aggidx"] = c(1:nrow(seedRaw@data))
seedRaw@data[,"aggidx2"] = c(1:nrow(seedRaw@data)) #this column used to merge seed
# if population field is null, set it to 0
if(length(which(is.na(seedRaw@data[, seedPopColName])))>0){
  seedRaw@data[which(is.na(seedRaw@data[, seedPopColName])), seedPopColName] = 0
}

if (is.projected(seedRaw)){
  seedPrj = seedRaw
  seedUnprj = spTransform(seedRaw,CRS(CONST_unprojected_proj4string))
} else {
  seedUnprj = seedRaw
  seedPrj = spTransform(seedRaw,CRS(CONST_projected_proj4string))
}

# seed must meed population threshold
seedFilter = seedUnprj@data[, seedPopColName] >= th_seed_minpop
seedDF = data.frame(seedUnprj[seedFilter,])
#seedPrjDF = data.frame(seedPrj[seedFilter,])
# extract prj and unprj coords for use
seedCoords_pj = data.frame(seedPrj)[, c("coords.x1","coords.x2")]
seedCoords_unpj = data.frame(seedUnprj)[, c("coords.x1","coords.x2")]


flag_seed_exist = FALSE
if (!is.null(nrow(seedDF))){
  if (nrow(seedDF) > 0) {
    flag_seed_exist = TRUE
  }
}
if (!flag_seed_exist){
  print("====== no valid seeds found, the selection criteria is too harsh =====")
  return()
}

flag_grid_exist = FALSE
if (!is.null(nrow(gridDF))){
  if (nrow(gridDF) > 0) {
    flag_grid_exist = TRUE
  }
}
if (!flag_grid_exist){
  print("====== no valid nonseeds found, the selection criteria is too harsh =====")
  return()
}

#route information data frame to record 
routeInfoDF = data.frame(nonSeedIdx=NULL,targetSeedIdx=NULL,eucDist=NULL,tvlDist=NULL,tvlTime=NULL)

for(i in gLoopStartIndex:nrow(gridDF)){
  
  gridId = gridDF[i,"gridId"]
  debugPrint(sprintf("[%i/%i]=====gridId: %i",i,nrow(gridDF),gridId))
  
  # if a nonseed area has low pop density than threshold, it is not agglomeratable, ignore it
  if (is.na(gridDF[i, gridDenColName])) {
    debugPrint("-- ignored (NA)")
    next
  }
  
  if (gridDF[i, gridDenColName] < th_popden) {
    debugPrint("-- ignored (popden too low)")
    next
  }
  
  # get lat-lot from unprojected grid
  s_lat = gridCoords_unpj[gridId, "coords.x2"]
  s_lon = gridCoords_unpj[gridId, "coords.x1"]
  #s_lat = attr(gridUnprj[gridId,],"coords")[2]
  #s_lon = attr(gridUnprj[gridId,],"coords")[1]
  
  targetSeedId = -1
  maxGravity = -1
  rtDist = -1
  rtTime = -1
  eucDist = -1
  # find the closest seed using gravity
  for(j in 1:nrow(seedDF)){
    seedId = seedDF[j,"seedId"]
    dist = sqrt((gridCoords_pj[gridId, "coords.x2"] - seedCoords_pj[seedId, "coords.x2"])^2 + (gridCoords_pj[gridId, "coords.x1"] - seedCoords_pj[seedId, "coords.x1"])^2)
    #dist = sqrt((attr(gridPrj[gridId,],"coords")[2] - attr(seedPrj[seedId,],"coords")[2])^2+(attr(gridPrj[gridId,],"coords")[1] - attr(seedPrj[seedId,],"coords")[1])^2)
   
    if (dist >= th_dist) next

    # calc and find the max gravity
    gravity = GeoTool.getGravity(massPara=seedDF[j, seedPopColName], distPara=dist, equationType=equationType)
    #gravity = seedDF[j, seedPopColName] / (dist * dist)
      
    if (maxGravity < gravity){
      targetSeedId = seedId
      maxGravity = gravity
      eucDist = dist
    }  
  }
  
  # if cannot find a seed around it, igore it
  if (targetSeedId < 0){
    debugPrint("-- ignored (cannot find an adjacent seed )")
    next
  }
  
  e_lat = seedCoords_unpj[targetSeedId, "coords.x2"]
  e_lon = seedCoords_unpj[targetSeedId, "coords.x1"]
  #e_lat = attr(seedUnprj[targetSeedId,],"coords")[2]
  #e_lon = attr(seedUnprj[targetSeedId,],"coords")[1]
  
  # test if route infomation already exists in gRouteInfoDF, if yes, fetch travel distance and time directly, otherwise, call apis
  cachedRouteInfo = RouteInfo.query(gridId, targetSeedId)
  flag_cached_found = FALSE
  if (!is.null(nrow(cachedRouteInfo))){
    if (nrow(cachedRouteInfo) > 0) {
      flag_cached_found = TRUE
    }
  }
  if (flag_cached_found){
    rtTime = cachedRouteInfo[1,"tvlTime"]
    rtDist = cachedRouteInfo[1,"tvlDist"]
    debugPrint("++++++++++++++ cached route info applied ++++++++++++++++")
  } else {
    
    # if gUseCachedRouteDBOnly is TURE and we cannot find route in cached DB, mark to be further corrected
    if (gUseCachedRouteDBOnly){
      debugPrint(sprintf("-- ignored (no route found in cached DB between [%.6f,%.6f] - [%.6f,%.6f] )",s_lat,s_lon,e_lat,e_lon))
      routeInfoDF<-rbind(routeInfoDF,data.frame(nonSeedIdx=gridId, targetSeedIdx=targetSeedId, eucDist=eucDist, tvlDist=-1, tvlTime=-1))
      next
    }
    
    MQDirectURL = sprintf(MapQuestDirectURLTemplate,s_lat,s_lon,e_lat,e_lon)
    #add keystring to mapquest request
    MQDirectURL = paste(MQDirectURL,MapQuestKeyString,sep="")
    GGDirectURL = sprintf(GoogleDirectURLTemplate,s_lat,s_lon,e_lat,e_lon)
    # MQRawJson is a list contains two attributes : route (list), info (list) . #attributes(MQRawJson)
    mqjsonstr = getURL(MQDirectURL)
    MQRawJson = fromJSON(mqjsonstr)
    
    # if cannot find a route with mapquest, try google
    if (MQRawJson$info$statuscode !=0 ){
      #
      ggjsonstr = getURL(GGDirectURL, .mapUnicode = FALSE)
      GGRawJson = fromJSON(ggjsonstr)
      if (GGRawJson$status == "OK"){
        debugPrint("*********** route find in google api *************")
        rtDist = GGRawJson$route[[1]]$legs[[1]]$distance$value / 1000
        rtTime = GGRawJson$route[[1]]$legs[[1]]$duration$value
        
        # test if big TER exists, if does, mark to be further corrected 
        if (rtDist/eucDist > gTERMax) {   
          debugPrint(sprintf("-- ignored (too big TER found between [%.6f,%.6f] - [%.6f,%.6f] )",s_lat,s_lon,e_lat,e_lon))
          routeInfoDF<-rbind(routeInfoDF,data.frame(nonSeedIdx=gridId, targetSeedIdx=targetSeedId, eucDist=eucDist, tvlDist=-1, tvlTime=-1))
          next
        }
        
        # save google route info to file
        routeJsonFilePath = sprintf("%s%s_%i_%i.json",routeInfoDir,"GG", gridId, targetSeedId)
        write(ggjsonstr,routeJsonFilePath)
        RouteInfo.append(gridId,targetSeedId,eucDist,rtDist,rtTime,"GG",routeJsonFilePath,routeInfoFilePath)
        
      } else {
        # if route cannot be found, try to using reverse geocoding api to re-generate both start and end location for new route query
        # try to find new start location
        isNewLocationApplied = FALSE
        isNewRouteFound = FALSE
        GGGeoCodingURL = sprintf(GoogleGeoCodingURLTemplate,s_lat,s_lon)
        GGGeoCodingRawJson = fromJSON(getURL(GGGeoCodingURL, .mapUnicode = FALSE))
        if (GGGeoCodingRawJson$status == "OK"){
          new_s_lat = GGGeoCodingRawJson$results[[1]]$geometry$location$lat
          new_s_lon = GGGeoCodingRawJson$results[[1]]$geometry$location$lng
          # test new location is close enough to the original location
          tmpDist = GeoTool.getLatLonDistance( new_s_lat, new_s_lon, s_lat, s_lon)
          if (tmpDist < th_geocoding_dist_shift) {
            # new location is not far away from origial one, use it
            s_lat = new_s_lat
            s_lon = new_s_lon
            isNewLocationApplied = TRUE
          }
        }
        
        # try to find new end location
        GGGeoCodingURL = sprintf(GoogleGeoCodingURLTemplate,e_lat,e_lon)
        GGGeoCodingRawJson = fromJSON(getURL(GGGeoCodingURL, .mapUnicode = FALSE))
        if (GGGeoCodingRawJson$status == "OK"){
          new_e_lat = GGGeoCodingRawJson$results[[1]]$geometry$location$lat
          new_e_lon = GGGeoCodingRawJson$results[[1]]$geometry$location$lng
          # test new location is close enough to the original location
          tmpDist = GeoTool.getLatLonDistance( new_e_lat, new_e_lon, e_lat, e_lon)
          if (tmpDist < th_geocoding_dist_shift) {
            # new location is not far away from origial one, use it
            e_lat = new_e_lat
            e_lon = new_e_lon
            isNewLocationApplied = TRUE
          }
        }
        
        # if either location is update, give it a chance to query the route again 
        if (isNewLocationApplied == TRUE){   
          GGDirectURL = sprintf(GoogleDirectURLTemplate,s_lat,s_lon,e_lat,e_lon)
          ggjsonstr = getURL(GGDirectURL, .mapUnicode = FALSE)
          GGRawJson = fromJSON(ggjsonstr)
          if (GGRawJson$status == "OK"){
            debugPrint("*********** route find in google api === after reverse geocoding *************")
            rtDist = GGRawJson$route[[1]]$legs[[1]]$distance$value / 1000
            rtTime = GGRawJson$route[[1]]$legs[[1]]$duration$value
            
            # test if big TER exists, if does, mark to be further corrected 
            if (rtDist/eucDist > gTERMax) {   
              debugPrint(sprintf("-- ignored (too big TER found between [%.6f,%.6f] - [%.6f,%.6f] )",s_lat,s_lon,e_lat,e_lon))
              routeInfoDF<-rbind(routeInfoDF,data.frame(nonSeedIdx=gridId, targetSeedIdx=targetSeedId, eucDist=eucDist, tvlDist=-1, tvlTime=-1))
              next
            }
            
            # save google route info to file
            routeJsonFilePath = sprintf("%s%s_%i_%i.json",routeInfoDir,"GG",gridId, targetSeedId)
            write(ggjsonstr,routeJsonFilePath)
            RouteInfo.append(gridId, targetSeedId,eucDist,rtDist,rtTime,"GG",routeJsonFilePath,routeInfoFilePath)
            
            isNewRouteFound = TRUE
          }
        }
        
        # if still cannot find a route, leave it (whose tvlTime will be set to -1) for further travel time estimation processing
        if (isNewRouteFound == FALSE) {   
          debugPrint(sprintf("-- ignored (no route found between [%.6f,%.6f] - [%.6f,%.6f] )",s_lat,s_lon,e_lat,e_lon))
          routeInfoDF<-rbind(routeInfoDF,data.frame(nonSeedIdx=gridId, targetSeedIdx=targetSeedId, eucDist=eucDist, tvlDist=-1, tvlTime=-1))
          next
        }
      }
      
    } else {
      route = MQRawJson$route
      rtDist = route$distance #unit in km
      rtTime = route$time #unit in second
      
      # test if big TER exists, if does, mark to be further corrected 
      if (rtDist/eucDist > gTERMax) {   
        debugPrint(sprintf("-- ignored (too big TER found between [%.6f,%.6f] - [%.6f,%.6f] )",s_lat,s_lon,e_lat,e_lon))
        routeInfoDF<-rbind(routeInfoDF,data.frame(nonSeedIdx=gridId, targetSeedIdx=targetSeedId, eucDist=eucDist, tvlDist=-1, tvlTime=-1))
        next
      }
      
      # save mapquest route info to file
      routeJsonFilePath = sprintf("%s%s_%i_%i.json",routeInfoDir,"MQ", gridId, targetSeedId)
      write(mqjsonstr,routeJsonFilePath)
      RouteInfo.append(gridId, targetSeedId, eucDist, rtDist,rtTime, "MQ", routeJsonFilePath, routeInfoFilePath)
    }
  }
  
  # test if the real travel time to target seed is short enough  
  if (rtTime >= th_tvltime){
    debugPrint(sprintf("-- ignored (too long to travel tvlTime:%.0f, tvlDist:%.3f )",rtTime, rtDist))
    next
  }
  
  # save the route infomation if a nonseed can be agglomerated to a seed 
  routeInfoDF<-rbind(routeInfoDF,data.frame(nonSeedIdx=gridId,targetSeedIdx=targetSeedId,eucDist=eucDist,tvlDist=rtDist,tvlTime=rtTime))
  
  # now the nonseed passes the agglomeratable test, agglomerate it to targetSeed by updating its aggidx
  gridUnprj@data[gridId,"aggidx"] = seedUnprj@data[targetSeedId,"aggidx"]
  gridUnprj@data[gridId,"aggidx2"] = seedUnprj@data[targetSeedId,"aggidx2"]
  
  #adm2@data[nonSeedIdx,"aggidx2"] = adm2@data[targetSeedIdx,"aggidx2"]
  debugPrint(sprintf("========================== grid[%i] is agglomerated to seed[%i]", gridId, targetSeedId))
  
}

# if no valid routes are found for the input parameters, exit process
if(nrow(routeInfoDF)==0){
  print("====== no valid route found between seeds and nonseeds, the selection criteria is too harsh =====")
  return()
}

# if valid routes are found for the input parameters, try to correct the issue records if exist

if(nrow(routeInfoDF)>0){
  
  # handle nonseeds whose agglomeratability cannot be determined yet by estimating travel time using simple equation
  # based on the known Euclidian distance and travel time between centroids in that country,  the estimated travel time is : eucDist * sumTvlTime / sumEucDist
  filter = routeInfoDF[,"tvlTime"] <= 0
  restnonseedDF = routeInfoDF[filter,]
  
  flag_restnonseed_exist = FALSE
  if (!is.null(nrow(restnonseedDF))){
    if (nrow(restnonseedDF) > 0) {
      flag_restnonseed_exist = TRUE
    }
  }
  
  if (flag_restnonseed_exist){
    sumEucDist = sum(routeInfoDF[!filter,"eucDist"])
    sumTvlTime = sum(routeInfoDF[!filter,"tvlTime"])
    if (sumEucDist > 0 ){
      ratio = sumTvlTime / sumEucDist
      for (i in 1:length(restnonseedDF[[1]])){
        if (restnonseedDF[i,"eucDist"] * ratio >= th_tvltime){
          debugPrint("-- ignored (too long to travel ---- final decision) ")
          next
        } else {
          gridId = restnonseedDF[i,"nonSeedIdx"]
          targetSeedId = restnonseedDF[i,"targetSeedIdx"]
          
          
          gridUnprj@data[gridId,"aggidx"] = seedUnprj@data[targetSeedId,"aggidx"]
          gridUnprj@data[gridId,"aggidx2"] = seedUnprj@data[targetSeedId,"aggidx2"]
          
          debugPrint(sprintf("========================== grid[%i] is agglomerated to seed[%i]", gridId, targetSeedId))
        }
      }
    }
  }
  
} else{
  # if no valid routes are found, the AI is directly computed based on seeds or merged seeds
  print("====== no valid route found between seeds and nonseeds, AI is directly computed based on seeds or merged seeds=====")
}

# save routeInfo
RouteInfo.save(routeInfoFilePath)

# seed merging happens here
# agglomarate seed if required
if (isSeedAgglomeratable == TRUE){
  
  aggSeedList = list()
  for(i in 1:length(seedPrj@data[seedFilter,"aggidx"])){
    aggSeedList[[i]] = c(seedPrj@data[seedFilter,"aggidx"][i])
  }
  
  
  testList  = aggSeedList
  # merge seed by "minimaldist" method
  if(seedMergeMethod == "minimaldist"){
    for(n in 1:length(testList)){
      
      if(length(testList[[n]])==1 & testList[[n]][1]==-1){
        next
      }
      
      for(m in 1:length(testList)){
        if (m == n){
          next
        }
        
        if (length(testList[[m]])==1 &testList[[m]][1]==-1){
          next
        }
        
        tmpMinDist = 999999999
        for(p in 1:length(testList[[n]])){
          
          lat1 = seedCoords_pj[testList[[n]][p], "coords.x2"]
          lon1 = seedCoords_pj[testList[[n]][p], "coords.x1"]
          
          for(q in 1:length(testList[[m]])){
            lat2 = seedCoords_pj[testList[[m]][q], "coords.x2"]
            lon2 = seedCoords_pj[testList[[m]][q], "coords.x1"] 
            
            dist = sqrt((lat1-lat2)^2+(lon1-lon2)^2)
            if(dist<tmpMinDist){
              tmpMinDist = dist
            }
          }
        }
        
        #if mindist is smaller than threshold, merge m to n, and clear m
        if(tmpMinDist < seedMergeDist*1000){
          testList[[n]] = c(testList[[n]], testList[[m]])
          testList[[m]] = c(-1)
        }
        
      }
      
    }
  }
  
  # merge seed by "exingravity" method: gravity = population / dist^2, where dist is in km
  if(seedMergeMethod == "exingravity"){
    #step1: external gravity calculation for each seed
    #for each seed s', find its neighbour s which meets 2 conditions: 
    #(1) pop(s) > pop(s')
    #(2) gravity(s',s) is the biggest gravity value among s' and its neighbours whose population is higher than s'
    tmpDF = data.frame(orgSeedId=seedPrj@data[seedFilter,"aggidx"],aggSeedId=-1,inG=-1, exG=-1, ssDist=-1, mergeFlag=FALSE)
    for(i in 1:nrow(tmpDF)){
      maxeG = -1
      aggSeedId = -1
      ssDist = -1
      lat1 = seedCoords_pj[tmpDF[i, "orgSeedId"], "coords.x2"]
      lon1 = seedCoords_pj[tmpDF[i, "orgSeedId"], "coords.x1"]
      for(j in 1:nrow(tmpDF)){
        #ignore if i=j
        if( i == j) next
        
        #ignore if pop(s') >= pop(s)
        if(seedPrj@data[tmpDF[i,"orgSeedId"],seedPopColName] >= seedPrj@data[tmpDF[j,"orgSeedId"],seedPopColName]) next
        
        lat2 = seedCoords_pj[tmpDF[j, "orgSeedId"], "coords.x2"]
        lon2 = seedCoords_pj[tmpDF[j, "orgSeedId"], "coords.x1"]
        eucDistSquare = (lat2-lat1)^2 + (lon2-lon1)^2
        
        #ignore if two seeds si and sj are too distant by comparing the educlidean distance between two closest grids attached to each seed. 
        shortestGridsEucDist = 9999999999
        
        # find grids whose aggid equals current seedid (si and sj)
        seed_i_gridFilter = gridUnprj@data[,"aggidx"] == tmpDF[i, "orgSeedId"]
        seed_i_gridIdVec = gridUnprj@data[seed_i_gridFilter, "gridId"]
        
        seed_j_gridFilter = gridUnprj@data[,"aggidx"] == tmpDF[j, "orgSeedId"]
        seed_j_gridIdVec = gridUnprj@data[seed_j_gridFilter, "gridId"]
        
        if(length(seed_i_gridIdVec) > 0 & length(seed_j_gridIdVec) > 0){
            for(m in 1:length(seed_i_gridIdVec)){
              lat_m = gridCoords_pj[seed_i_gridIdVec[m], "coords.x2"] 
              lon_m = gridCoords_pj[seed_i_gridIdVec[m], "coords.x1"]
             
              for(n in 1:length(seed_j_gridIdVec)){
                lat_n = gridCoords_pj[seed_j_gridIdVec[n], "coords.x2"] 
                lon_n = gridCoords_pj[seed_j_gridIdVec[n], "coords.x1"]
                
                tmpEucDist = sqrt((lat_m-lat_n)^2 + (lon_m-lon_n)^2)
                
                if (shortestGridsEucDist > tmpEucDist) shortestGridsEucDist = tmpEucDist
              }
            }
            # ignore if they are too distant
            if(shortestGridsEucDist > seedMergeDist*1000) next
        } else {
          next
        }
        
        if(eucDistSquare < 1.0) {
          tmpeG = 999999999
        } else {
          tmpeG = GeoTool.getGravity(massPara=seedPrj@data[tmpDF[j,"orgSeedId"],seedPopColName], distPara=sqrt(eucDistSquare)/1000)
        }
        
        if(tmpeG > maxeG){
          maxeG = tmpeG
          aggSeedId = tmpDF[j,"orgSeedId"]
          ssDist = sqrt(eucDistSquare)
        }
      }
      
      tmpDF[i,"aggSeedId"] = aggSeedId
      tmpDF[i,"ssDist"] = ssDist
      tmpDF[i,"exG"] = maxeG
      
    }
    
    #step2: internal gravity calculation for each seed, using all aggregated grids of seed s' to calculate internal gravity
    for(i in 1:nrow(tmpDF)){
      inG = 0.0
      lat1 = seedCoords_pj[tmpDF[i, "orgSeedId"], "coords.x2"] 
      lon1 = seedCoords_pj[tmpDF[i, "orgSeedId"], "coords.x1"]
      
      # find all grids whose aggid equals current seedid
      candidateGridFilter = gridUnprj@data[,"aggidx"] == tmpDF[i, "orgSeedId"]
      candidateGridIdVec = gridUnprj@data[candidateGridFilter, "gridId"]
      
      # if there is no grid belongs to this seed
      if(length(candidateGridIdVec) == 0){
        print(sprintf("=== no grid belongs to seed[%i]", tmpDF[i, "orgSeedId"]))
        next
      }
        
      for(j in 1:length(candidateGridIdVec)){
        lat2 = gridCoords_pj[candidateGridIdVec[j], "coords.x2"] 
        lon2 = gridCoords_pj[candidateGridIdVec[j], "coords.x1"] 
        eucDist = sqrt((lat2-lat1)^2 + (lon2-lon1)^2)
        
        #if a grid is too close to the seed, igore this grid
        if(eucDist <= gridEdgeLength * 1000) next
        
        #otherwise, sum up the gravity
        inG = inG + GeoTool.getGravity(massPara=gridUnprj@data[candidateGridIdVec[j],gridPopColName], distPara=eucDist/1000)
      }
      
      
      if(inG > 0){
        tmpDF[i,"inG"] = inG
      }
    }
    
    #step3: update mergeflag
    filter =tmpDF[,"inG"] < tmpDF[,"exG"]
    tmpDF[filter, "mergeFlag"] = TRUE
    #update those unmergable seed's aggSeedId to its own seedid
    tmpDF[!filter, "aggSeedId"] = tmpDF[!filter, "orgSeedId"]
    
    #step4: update aggSeedId: 2->1 4->2 ==> 2->1 4->1
    for(i in 1:nrow(tmpDF)){
      
      if(tmpDF[i, "mergeFlag"] == FALSE) next
      
      # find all aggSeedId==orgSeedId records, update their aggSeedId to current orgSeedId's aggSeedId
      orgSeedId = tmpDF[i, "orgSeedId"]
      aggSeedId = tmpDF[i, "aggSeedId"]
      
      tmpfilter = tmpDF[, "aggSeedId"] == orgSeedId
      tmpDF[tmpfilter, "aggSeedId"] = aggSeedId
      
    }
    
    #step5: update testList
    uniqueSeedVec = tmpDF[,"aggSeedId"]
    uniqueSeedVec = uniqueSeedVec[!duplicated(uniqueSeedVec)]
    for(i in 1: length(testList)){
      if(testList[[i]] %in% uniqueSeedVec){
        f = tmpDF[,"aggSeedId"]==testList[[i]]
        testList[[i]] = tmpDF[f, "orgSeedId"]
      } else {
        testList[[i]] = c(-1)
      }
    }
  }
  
  aggSeedList = testList
  
  # agglomerate seed
  for (i in 1:length(aggSeedList)){
    
    #skip cleared list element
    if (length(aggSeedList[[i]])==1 & aggSeedList[[i]][1]==-1){
      next
    }
    
    # by default, merge to the smallest idx seed
    aggSeedIdx = min(aggSeedList[[i]])
    
    # or merge to the highest population seed
    if (seedMergeTo == "highestPop") {
      highestPopValue = -1
      for (tmpIdx in aggSeedList[[i]]){
        if (seedPrj@data[tmpIdx, seedPopColName] > highestPopValue){
          aggSeedIdx = tmpIdx
          highestPopValue = seedPrj@data[tmpIdx, seedPopColName]
        }
      }
    } else if (seedMergeTo == "bboxCentre"){ # or merge to the geo central seed
      if(length(aggSeedList[[i]]) == 1){#for seed group contains only a single seed, just use the seed
        aggSeedIdx = aggSeedList[[i]][1]
      } else if (length(aggSeedList[[i]]) == 2){#for seed group contains only 2 seeds, just "highestPop" one
        highestPopValue = -1
        for (tmpIdx in aggSeedList[[i]]){
          if (seedPrj@data[tmpIdx, seedPopColName] > highestPopValue){
            aggSeedIdx = tmpIdx
            highestPopValue = seedPrj@data[tmpIdx, seedPopColName]
          }
        }
      } else {#for seed group contains more than 2 seeds, find the central one
        
        #coords = attr(seedPrj[aggSeedList[[i]],],"coords")
        coords = seedCoords_pj[aggSeedList[[i]],]
        coords = data.frame(coords)
        minx1 = min(coords[,"coords.x1"])
        maxx1 = max(coords[,"coords.x1"])
        minx2 = min(coords[,"coords.x2"])
        maxx2 = max(coords[,"coords.x2"])
        centralx1 = (minx1 + maxx1)/2
        centralx2 = (minx2 + maxx2)/2
        minAbsDist = 99999999
        for (tmpIdx in aggSeedList[[i]]){
          tmpAbsDist = abs(centralx1 - seedCoords_pj[tmpIdx, "coords.x1"]) + abs(centralx2 - seedCoords_pj[tmpIdx, "coords.x2"])
          if (tmpAbsDist < minAbsDist){
            aggSeedIdx = tmpIdx
            minAbsDist = tmpAbsDist
          }
        }
      }
    } 
    
    vec = aggSeedList[[i]]
    vec = vec[which(vec!=aggSeedIdx)]
    seedPrj@data[vec,"aggidx2"] = seedPrj@data[aggSeedIdx,"aggidx2"]
    seedUnprj@data[vec,"aggidx2"] = seedUnprj@data[aggSeedIdx,"aggidx2"]
    
  }
}

# then we need update aggidx2 in the gridUnprj@data
# identify all aggregated seed
filter = seedPrj@data[ ,"aggidx"] != seedPrj@data[ ,"aggidx2"]
aggSeedDF = seedPrj@data[filter ,c("aggidx","aggidx2")]
# replace aggidx2 
for(i in 1:nrow(aggSeedDF)){
    f = gridUnprj@data[,"aggidx"] == aggSeedDF[i, "aggidx"]
    gridUnprj@data[f,"aggidx2"] = aggSeedDF[i, "aggidx2"]
}

# calc AI based on seed
rltDataFrame = data.frame(seedIdx=NULL,districtName=NULL,AI=NULL,sumPop=NULL, sumArea=NULL)
df = seedUnprj@data
for (i in 1:nrow(df)){
  seedId = df[i, "seedId"] #attr(df[i,], "row.names")
  districtName = df[i, seedNameColName]
  filter = gridUnprj@data[, "aggidx"] == df[i, "aggidx"]
  sumPop = sum(gridUnprj@data[filter, gridPopColName])
  sumArea =  nrow(gridUnprj@data[filter, ]) / nrow(gridUnprj@data)
  AI = sumPop / sum(gridUnprj@data[, gridPopColName])
  rltDataFrame<-rbind(rltDataFrame,data.frame(seedIdx=seedId, districtName=districtName, AI=AI, sumPop=sumPop, sumArea=sumArea))
}
#rltDataFrame$AI = format(rltDataFrame$AI, nsmall=4, digits=4, scientific = FALSE)
write.table(rltDataFrame, file=sprintf("%s/AI_%i_%i_%i_%s_%s_orgseed.csv", outShpFileDir, thPopDen, thSeedMinPop, thTvlTime, seedMergeMethod, equationType), row.names = FALSE, sep=",")


# calc AI based on seed2 (agglomerated seed)
rltDataFrame = data.frame(seedIdx=NULL,districtName=NULL,AI=NULL,sumPop=NULL, sumArea=NULL)

aggSeedIdxVec = seedUnprj@data[,"aggidx2"]
aggSeedIdxVec = aggSeedIdxVec[!duplicated(aggSeedIdxVec)]

df = seedUnprj@data[aggSeedIdxVec[!duplicated(aggSeedIdxVec)], ]
for (i in 1:nrow(df)){
  seedId = df[i, "seedId"] #attr(df[i,], "row.names")
  districtName = df[i, seedNameColName]
  filter = gridUnprj@data[, "aggidx2"] == df[i, "aggidx2"]
  sumPop = sum(gridUnprj@data[filter, gridPopColName])
  sumArea =  nrow(gridUnprj@data[filter, ]) / nrow(gridUnprj@data)
  AI = sumPop / sum(gridUnprj@data[, gridPopColName])
  rltDataFrame<-rbind(rltDataFrame,data.frame(seedIdx=seedId, districtName=districtName, AI=AI, sumPop=sumPop, sumArea=sumArea))
}

#rltDataFrame$AI = format(rltDataFrame$AI, nsmall=4, digits=4, scientific = FALSE)
write.table(rltDataFrame, file=sprintf("%s/AI_%i_%i_%i_%s_%s_aggseed.csv", outShpFileDir, thPopDen, thSeedMinPop, thTvlTime, seedMergeMethod, equationType), row.names = FALSE, sep=",")

writeOGR(obj=gridUnprj, dsn=outShpFileDir, layer=sprintf("AI_%i_%i_%i_%s_%s", thPopDen, thSeedMinPop, thTvlTime, seedMergeMethod, equationType), driver="ESRI Shapefile", check_exists=TRUE, overwrite_layer=TRUE)

algEndTime = Sys.time()

print(sprintf("==========> all done (in %.2f seconds) <==========", as.numeric(algEndTime-algStartTime, units="secs")))
}

# generate Agglomeration Index based on single grid file. (seeds are selected from grids on condition)
f_genAI_2 <- function(dsn = "./data/srilanka/", 
                      gridFileName = "lkadensp00ag", 
                      gridDenColName = "DEN",
                      gridPopColName = "POP",
                      outDir = gOutRootDir,
                      thPopDen = 150, 
                      thSeedMinPop = 10000, 
                      thTvlTime = 60, 
                      thSearchSeedRadius = 80, 
                      thGeoCodingDistShift = 1,
                      seedAsTopNHighPopArea = -1, 
                      seedDirName = "ByTopPop",
                      countryName = gCountryName,
                      dataYear = gDataYear,
                      seedMergeDist = 7,
                      seedMergeTo = "highestPop",
                      seedMergeMethod = "exingravity",
                      gridEdgeLength = 4.5,
                      equationType = "SQUAREDDIST"
){
  # # # # # # # # # # # # # # # # # # # # # # # # # # # #
  # Input parameters:
  # (1) dsn: the root directory of data sets
  # (2) gridFileName: grid data (points in shp file) file name..
  # (3) gridDenColName: grid population density column name.
  # (4) gridPopColName: grid population column name
  # (5) outDir: the root directory of calculation outputs
  # (6) thPopDen: threshold of population density. A non-seed area is only considered as agglomeratable if its popden is bigger than this threshold. unit: the number of people in 1 square km
  # (7) thSeedMinPop: threshold of population. A seed area is only considered and used as an agglomeration core if its population is larger than this threshold. 
  # (8) thTvlTime (minute): threshold of travel time between seed and non-seed districts. unit: minute
  # (9) thSearchSeedRadius (km): threshold of the Euclidian distance between a non-seed and its potential seeds. Those too distant seeds will be excluded from the gravity calculation.
  # (10) seedAsTopNHighPopArea: the number of top population areas to be selected as seeds. Default value is -1, which means all qualified seeds will be in use.
  # (11) thGeoCodingDistShift (km):threshold of the Euclidian distance between the original point and reverse geocoding point. If the reverse geocoding point is too distant away from the original one, it will not be used.
  # (12) seedDirName: for different seed selections, the result will be put into different output directories This is the directory name for a particular seed selection. It can be any valid and meaningful folder name, no whitespace in it.
  # (13) countryName: the name of the country. It is used as a part of the outputs path
  # (14) dataYear: the year of population data.  It is used as a part of the outputs path
  # (15) seedMergeDist: distance threshold for seeds merge (Unit: km) This parameter will be ignored if seedMergeMethod is set to "exingravity"
  #      (For CIESIN grid data of Sri Lanka, the direct distance between two neighbour grid is 4.58 = sqrt(21), and the diagonal distance is 6.48 = sqrt(21)*sqrt(2), set this threshold value to 7 so that two grids within diagonal distance are still aggregatable )
  # (16) seedMergeTo: "smallestIdx": all mergeable seeds will be merged to the seed whose idx is the smallest; 
  #                   "bboxCentre": among all mergeable seeds, find one who is closeast to thire bbox centre. All other seeds will be aggragated to this 'central seed'
  #                   "highestPop"(default): all mergeable seeds will be merged to the seed whose population is the highest; 
  #                   "highestPopDen": all mergeable seeds will be merged to the seed whose population density is the highest
  # (17) seedMergeMethod: if set to "minimaldist", two closest seeds will be merged if their distance is within the seedMergeDist; if set to "exingravity", and if a seed's internal gravity is bigger than its external gravity, it remains independent
  # (18) gridEdgeLength: unit (km), the length of grid cell edge. Vary on different grid dataset. For Srilanka, it is 4.5km
  # Output:
  # (1) shp files containing agglomeration index information
  # (2) a calculated route data folder ("routeinfo") containing raw route request api results and tavelinfo database "db.csv"
  # (3) a calculated inner centroid data file ("innerCentroids.csv") 
  # (4) two AI tables for original seed ("AI_XX_XX_XX_orgseed.csv") and aggregated seed ("AI_XX_XX_XX_aggseed.csv") 
  # # # # # # # # # # # # # # # # # # # # # # # # # # # #
  
  algStartTime = Sys.time()
  
  # create a folder to hold route information 
  routeInfoDir = sprintf("%s%s/genAI_2/%s/",outDir,countryName,"routeinfo")
  dir.create(routeInfoDir, showWarnings=FALSE, recursive=TRUE)
  routeInfoFilePath = sprintf("%s%s",routeInfoDir,"db.csv")
  
  # load route info into gRouteInfoDF
  RouteInfo.load(routeInfoFilePath)
  
  # create a folder to AI results (shp files) for different seed choices
  outShpFileDir = sprintf("%s%s/genAI_2/%s/%s",outDir, countryName, dataYear, seedDirName)
  dir.create(outShpFileDir, showWarnings=FALSE, recursive=TRUE)
  
  # set TRUE to enable seeds agglomeration 
  isSeedAgglomeratable = TRUE
  
  # define thresholds 
  # POP DENSITY: run an AI at each of these minimum levels: 150, 300, and 500 people per square kilometre
  # TRAVEL TIME: run an AI at each of these maximum levels: 30, 60, and 90 minutes
  # MINIMUM SEED POPULATION: run an AI at each of these minimum levels: 20,000, 50,000, 100,000, and 500,000.
  th_popden = thPopDen
  th_tvltime = thTvlTime*60
  th_seed_minpop = thSeedMinPop # the minimum population to be considered as a seed
  
  # Eclidian distance to search seeds around a non-seed. Unit: meter. It is used first to reduce real distance computation
  th_dist = thSearchSeedRadius*1000
  # the maximum Euclidian distance between an orginal point and its reverse geocoding point, if the distance bigger than this threshold, the reverse geocoding point will not be used
  th_geocoding_dist_shift = thGeoCodingDistShift*1000 
 
  
  # load grids
  gridRaw <- readOGR(dsn=dsn,layer=gridFileName,encoding="utf8", verbose=FALSE)
  # create a gridId column
  gridRaw@data[,"gridId"] = c(1:nrow(gridRaw@data))
  # add additional columns : aggidx (default 0), aggidx2 (default 0, when seed agglomeration applied) 
  gridRaw@data[,"aggidx"] = 0
  gridRaw@data[,"aggidx2"] = 0
  gridRaw@data[,"isseed"] = 0
  gridRaw@data[,"isseed2"] = 0
  # if population or density field is null, set it to 0
  if(length(which(is.na(gridRaw@data[, gridDenColName])))>0){
    gridRaw@data[which(is.na(gridRaw@data[, gridDenColName])), gridDenColName] = 0
  }
  if(length(which(is.na(gridRaw@data[, gridPopColName])))>0){
    gridRaw@data[which(is.na(gridRaw@data[, gridPopColName])), gridPopColName] = 0
  }
  
  if (is.projected(gridRaw)){
    gridPrj = gridRaw
    gridUnprj = spTransform(gridRaw,CRS(CONST_unprojected_proj4string))
  } else {
    gridUnprj = gridRaw
    gridPrj = spTransform(gridRaw,CRS(CONST_projected_proj4string))
  }
  
  gridDF = data.frame(gridUnprj[,])
  
  # load centroids for use
  centroids = data.frame(gridUnprj[,])[,c("coords.x1","coords.x2")]
  centroids_pj = data.frame(gridPrj[,])[,c("coords.x1","coords.x2")]
  
  # find seeds
  # seed must meed population threshold
  seedPopFilter = gridDF[, gridPopColName] > th_seed_minpop
  
  # choose seed by top N population districts
  topN = seedAsTopNHighPopArea
  
  if ((topN > nrow(gridDF)) | (topN <= 0)) topN = nrow(gridDF)
  
  tmpOrdered = as.vector(gridDF[ order(-gridDF[,gridPopColName]), ][1:topN, gridPopColName])
  seedFilter = seedPopFilter & gridDF[, gridPopColName] %in% tmpOrdered
  seedFilter = ifelse(is.na(seedFilter), FALSE, seedFilter)
  
  #separate seed and nonseed dataframe
  seedDF = gridDF[seedFilter,]
  nonseedDF = gridDF[!seedFilter,]
  
  flag_seed_exist = FALSE
  if (!is.null(nrow(seedDF))){
    if (nrow(seedDF) > 0) {
      flag_seed_exist = TRUE
    }
  }
  if (!flag_seed_exist){
    print("====== no valid seeds found, the selection criteria is too harsh =====")
    return()
  }
  
  flag_nonseed_exist = FALSE
  if (!is.null(nrow(nonseedDF))){
    if (nrow(nonseedDF) > 0) {
      flag_nonseed_exist = TRUE
    }
  }
  if (!flag_nonseed_exist){
    print("====== no valid nonseeds found, the selection criteria is too harsh =====")
    return()
  }
  
  gridUnprj@data[seedFilter,"isseed"] = 1 # set isseed flag, and mark seed's aggidx as it rowname
  gridUnprj@data[seedFilter,"isseed2"] = 0 # set agglomerated seed index will be assigned later
  gridUnprj@data[seedFilter,"aggidx"] = gridUnprj@data[seedFilter,"gridId"] #attr(adm2@data[seedFilter,], "row.names")
  gridUnprj@data[seedFilter,"aggidx2"] = gridUnprj@data[seedFilter,"gridId"] #attr(adm2@data[seedFilter,], "row.names")
  
  #route information data frame to record 
  routeInfoDF = data.frame(nonSeedIdx=NULL,targetSeedIdx=NULL,eucDist=NULL,tvlDist=NULL,tvlTime=NULL)
  
  for(i in gLoopStartIndex:nrow(nonseedDF)){
    
    nonSeedIdx = nonseedDF[i,"gridId"] #attr(nonseedDF[i,], "row.names")
    debugPrint(sprintf("[%i/%i]=====nonseedidx: %i", i, nrow(nonseedDF), nonSeedIdx))
    
    # if a nonseed area has low pop density than threshold, it is not agglomeratable, ignore it
    if (is.na(nonseedDF[i,gridDenColName])) {
      debugPrint("-- ignored (NA)")
      next
    }
    
    if (nonseedDF[i,gridDenColName] < th_popden) {
      debugPrint("-- ignored (popden too low)")
      next
    }
    
    s_lat = centroids[nonSeedIdx,"coords.x2"]
    s_lon = centroids[nonSeedIdx,"coords.x1"]
    
    targetSeedIdx = -1
    maxGravity = -1
    rtDist = -1
    rtTime = -1
    eucDist = -1
    # find the closest seed using gravity
    for(j in 1:nrow(seedDF)){
      seedIdx = seedDF[j,"gridId"] #attr(seedDF[j,], "row.names")
      dist = sqrt((centroids_pj[seedIdx,"coords.x2"] - centroids_pj[nonSeedIdx,"coords.x2"])^2 + (centroids_pj[seedIdx,"coords.x1"] - centroids_pj[nonSeedIdx,"coords.x1"])^2)
      if (dist >= th_dist) next
      
      # calc and find the max gravity
      gravity = GeoTool.getGravity(massPara=seedDF[j,gridPopColName], distPara=dist, equationType=equationType)
      #gravity = seedDF[j,gridPopColName] / (dist * dist)
      if (maxGravity < gravity){
        targetSeedIdx = seedIdx
        maxGravity = gravity
        eucDist = dist
      }  
    }
    
    # if cannot find a seed around it, igore it
    if (targetSeedIdx < 0){
      debugPrint("-- ignored (cannot find an adjacent seed )")
      next
    }
    
    e_lat = centroids[targetSeedIdx,"coords.x2"]
    e_lon = centroids[targetSeedIdx,"coords.x1"]
    
    # test if route infomation already exists in gRouteInfoDF, if yes, fetch travel distance and time directly, otherwise, call apis
    cachedRouteInfo = RouteInfo.query(nonSeedIdx, targetSeedIdx)
    flag_cached_found = FALSE
    if (!is.null(nrow(cachedRouteInfo))){
      if (nrow(cachedRouteInfo) > 0) {
        flag_cached_found = TRUE
      }
    }
    if (flag_cached_found){
      rtTime = cachedRouteInfo[1,"tvlTime"]
      rtDist = cachedRouteInfo[1,"tvlDist"]
      debugPrint("++++++++++++++ cached route info applied ++++++++++++++++")
    } else {
      
      # if gUseCachedRouteDBOnly is TURE and we cannot find route in cached DB, mark to be further corrected
      if (gUseCachedRouteDBOnly){
        debugPrint(sprintf("-- ignored (no route found in cached DB between [%.6f,%.6f] - [%.6f,%.6f] )",s_lat,s_lon,e_lat,e_lon))
        routeInfoDF<-rbind(routeInfoDF,data.frame(nonSeedIdx=nonSeedIdx, targetSeedIdx=targetSeedIdx, eucDist=eucDist, tvlDist=-1, tvlTime=-1))
        next
      }
      
      MQDirectURL = sprintf(MapQuestDirectURLTemplate,s_lat,s_lon,e_lat,e_lon)
      #add keystring to mapquest request
      MQDirectURL = paste(MQDirectURL,MapQuestKeyString,sep="")
      GGDirectURL = sprintf(GoogleDirectURLTemplate,s_lat,s_lon,e_lat,e_lon)
      # MQRawJson is a list contains two attributes : route (list), info (list) . #attributes(MQRawJson)
      mqjsonstr = getURL(MQDirectURL)
      MQRawJson = fromJSON(mqjsonstr)
      
      # if cannot find a route with mapquest, try google
      if (MQRawJson$info$statuscode !=0 ){
        #
        ggjsonstr = getURL(GGDirectURL, .mapUnicode = FALSE)
        GGRawJson = fromJSON(ggjsonstr)
        if (GGRawJson$status == "OK"){
          debugPrint("*********** route find in google api *************")
          rtDist = GGRawJson$route[[1]]$legs[[1]]$distance$value / 1000
          rtTime = GGRawJson$route[[1]]$legs[[1]]$duration$value
          
          # test if big TER exists, if does, mark to be further corrected 
          if (rtDist/eucDist > gTERMax) {   
            debugPrint(sprintf("-- ignored (too big TER found between [%.6f,%.6f] - [%.6f,%.6f] )",s_lat,s_lon,e_lat,e_lon))
            routeInfoDF<-rbind(routeInfoDF,data.frame(nonSeedIdx=nonSeedIdx, targetSeedIdx=targetSeedIdx, eucDist=eucDist, tvlDist=-1, tvlTime=-1))
            next
          }
          # save google route info to file
          routeJsonFilePath = sprintf("%s%s_%i_%i.json",routeInfoDir,"GG",nonSeedIdx, targetSeedIdx)
          write(ggjsonstr,routeJsonFilePath)
          RouteInfo.append(nonSeedIdx,targetSeedIdx,eucDist,rtDist,rtTime,"GG",routeJsonFilePath,routeInfoFilePath)
          
        } else {
          # if route cannot be found, try to using reverse geocoding api to re-generate both start and end location for new route query
          # try to find new start location
          isNewLocationApplied = FALSE
          isNewRouteFound = FALSE
          GGGeoCodingURL = sprintf(GoogleGeoCodingURLTemplate,s_lat,s_lon)
          GGGeoCodingRawJson = fromJSON(getURL(GGGeoCodingURL, .mapUnicode = FALSE))
          if (GGGeoCodingRawJson$status == "OK"){
            new_s_lat = GGGeoCodingRawJson$results[[1]]$geometry$location$lat
            new_s_lon = GGGeoCodingRawJson$results[[1]]$geometry$location$lng
            # test new location is close enough to the original location
            tmpDist = GeoTool.getLatLonDistance( new_s_lat, new_s_lon, s_lat, s_lon)
            if (tmpDist < th_geocoding_dist_shift) {
              # new location is not far away from origial one, use it
              s_lat = new_s_lat
              s_lon = new_s_lon
              isNewLocationApplied = TRUE
            }
          }
          
          # try to find new end location
          GGGeoCodingURL = sprintf(GoogleGeoCodingURLTemplate,e_lat,e_lon)
          GGGeoCodingRawJson = fromJSON(getURL(GGGeoCodingURL, .mapUnicode = FALSE))
          if (GGGeoCodingRawJson$status == "OK"){
            new_e_lat = GGGeoCodingRawJson$results[[1]]$geometry$location$lat
            new_e_lon = GGGeoCodingRawJson$results[[1]]$geometry$location$lng
            # test new location is close enough to the original location
            tmpDist = GeoTool.getLatLonDistance( new_e_lat, new_e_lon, e_lat, e_lon)
            if (tmpDist < th_geocoding_dist_shift) {
              # new location is not far away from origial one, use it
              e_lat = new_e_lat
              e_lon = new_e_lon
              isNewLocationApplied = TRUE
            }
          }
          
          # if either location is update, give it a chance to query the route again 
          if (isNewLocationApplied == TRUE){   
            GGDirectURL = sprintf(GoogleDirectURLTemplate,s_lat,s_lon,e_lat,e_lon)
            ggjsonstr = getURL(GGDirectURL, .mapUnicode = FALSE)
            GGRawJson = fromJSON(ggjsonstr)
            if (GGRawJson$status == "OK"){
              debugPrint("*********** route find in google api === after reverse geocoding *************")
              rtDist = GGRawJson$route[[1]]$legs[[1]]$distance$value / 1000
              rtTime = GGRawJson$route[[1]]$legs[[1]]$duration$value
              
              # test if big TER exists, if does, mark to be further corrected 
              if (rtDist/eucDist > gTERMax) {   
                debugPrint(sprintf("-- ignored (too big TER found between [%.6f,%.6f] - [%.6f,%.6f] )",s_lat,s_lon,e_lat,e_lon))
                routeInfoDF<-rbind(routeInfoDF,data.frame(nonSeedIdx=nonSeedIdx, targetSeedIdx=targetSeedIdx, eucDist=eucDist, tvlDist=-1, tvlTime=-1))
                next
              }
              
              # save google route info to file
              routeJsonFilePath = sprintf("%s%s_%i_%i.json",routeInfoDir,"GG",nonSeedIdx, targetSeedIdx)
              write(ggjsonstr,routeJsonFilePath)
              RouteInfo.append(nonSeedIdx,targetSeedIdx,eucDist,rtDist,rtTime,"GG",routeJsonFilePath,routeInfoFilePath)
              
              isNewRouteFound = TRUE
            }
          }
          
          # if still cannot find a route, leave it (whose tvlTime will be set to -1) for further travel time estimation processing
          if (isNewRouteFound == FALSE) {   
            debugPrint(sprintf("-- ignored (no route found between [%.6f,%.6f] - [%.6f,%.6f] )",s_lat,s_lon,e_lat,e_lon))
            routeInfoDF<-rbind(routeInfoDF,data.frame(nonSeedIdx=nonSeedIdx, targetSeedIdx=targetSeedIdx, eucDist=eucDist, tvlDist=-1, tvlTime=-1))
            next
          }
        }
        
      } else {
        route = MQRawJson$route
        rtDist = route$distance #unit in km
        rtTime = route$time #unit in second
        
        # test if big TER exists, if does, mark to be further corrected 
        if (rtDist/eucDist > gTERMax) {   
          debugPrint(sprintf("-- ignored (too big TER found between [%.6f,%.6f] - [%.6f,%.6f] )",s_lat,s_lon,e_lat,e_lon))
          routeInfoDF<-rbind(routeInfoDF,data.frame(nonSeedIdx=nonSeedIdx, targetSeedIdx=targetSeedIdx, eucDist=eucDist, tvlDist=-1, tvlTime=-1))
          next
        }
        
        # save mapquest route info to file
        routeJsonFilePath = sprintf("%s%s_%i_%i.json",routeInfoDir,"MQ",nonSeedIdx, targetSeedIdx)
        write(mqjsonstr,routeJsonFilePath)
        RouteInfo.append(nonSeedIdx, targetSeedIdx, eucDist, rtDist,rtTime, "MQ", routeJsonFilePath,routeInfoFilePath)
      }
    }
    
    # test if the real travel time to target seed is short enough  
    if (rtTime >= th_tvltime){
      debugPrint(sprintf("-- ignored (too long to travel tvlTime:%.0f, tvlDist:%.3f )",rtTime, rtDist))
      next
    }
    
    # save the route infomation if a nonseed can be agglomerated to a seed 
    routeInfoDF<-rbind(routeInfoDF,data.frame(nonSeedIdx=nonSeedIdx,targetSeedIdx=targetSeedIdx,eucDist=eucDist,tvlDist=rtDist,tvlTime=rtTime))
    
    # now the nonseed passes the agglomeratable test, agglomerate it to targetSeed by updatint its aggidx
    gridUnprj@data[nonSeedIdx,"aggidx"] = gridUnprj@data[targetSeedIdx,"aggidx"]
    gridUnprj@data[nonSeedIdx,"aggidx2"] = gridUnprj@data[targetSeedIdx,"aggidx2"]
    debugPrint(sprintf("========================== [%i] is agglomerated to [%i]", nonSeedIdx, targetSeedIdx))
    
  }
  
  # if no valid routes are found for the input parameters, exit process
  if(nrow(routeInfoDF)==0){
    print("====== no valid route found between seeds and nonseeds, the selection criteria is too harsh =====")
    return()
  }
  
  # if valid routes are found for the input parameters, try to correct the issue records if exist
  
  if(nrow(routeInfoDF)>0){
    
    # handle nonseeds whose agglomeratability cannot be determined yet by estimating travel time using simple equation
    # based on the known Euclidian distance and travel time between centroids in that country,  the estimated travel time is : eucDist * sumTvlTime / sumEucDist
    filter = routeInfoDF[,"tvlTime"] < 0
    restnonseedDF = routeInfoDF[filter,]
    
    flag_restnonseed_exist = FALSE
    if (!is.null(nrow(restnonseedDF))){
      if (nrow(restnonseedDF) > 0) {
        flag_restnonseed_exist = TRUE
      }
    }
    
    if (flag_restnonseed_exist){
      sumEucDist = sum(routeInfoDF[!filter,"eucDist"])
      sumTvlTime = sum(routeInfoDF[!filter,"tvlTime"])
      if (sumEucDist > 0 ){
        ratio = sumTvlTime / sumEucDist
        for (i in 1:length(restnonseedDF[[1]])){
          if (restnonseedDF[i,"eucDist"] * ratio >= th_tvltime){
            debugPrint("-- ignored (too long to travel ---- final decision) ")
            next
          } else {
            nonSeedIdx = restnonseedDF[i,"nonSeedIdx"]
            targetSeedIdx = restnonseedDF[i,"targetSeedIdx"]
            
            gridUnprj@data[nonSeedIdx,"aggidx"] = gridUnprj@data[targetSeedIdx,"aggidx"]
            gridUnprj@data[nonSeedIdx,"aggidx2"] = gridUnprj@data[targetSeedIdx,"aggidx2"]
            debugPrint(sprintf("========================== [%i] is agglomerated to [%i] ---- final decision", nonSeedIdx, targetSeedIdx))
          }
        }
      }
    }
    
  }
  else{
    # if no valid routes are found, the AI is directly computed based on seeds or merged seeds
    print("====== no valid route found between seeds and nonseeds, AI is directly computed based on seeds or merged seeds=====")
  }
  
  # save routeInfo
  RouteInfo.save(routeInfoFilePath)
  
  # seed merging happens here
  # agglomarate seed if required
  if (isSeedAgglomeratable == TRUE){
    
    aggSeedList = list()
    for(i in 1:length(gridUnprj@data[seedFilter,"aggidx"])){
      aggSeedList[[i]] = c(gridUnprj@data[seedFilter,"aggidx"][i])
    }
    
    testList  = aggSeedList
    # this flag controls the outer while-loop, making sure that all seeds are properly aggregated. 
    # the inner two nested for-loops start from the head of testList, testing distance between seeds from two seed groups:seeds-m and seeds-n 
    # each seed group contains one or more seeds. seeds in a same seed group will eventually aggregate as a single seed.
    # if, for example, a seed (seeds-n-1) in group seeds-n is found within seedMergeDist of any one of seed in group seeds-m, all seeds in group seeds-n will be merged to group seeds-m.
    # In this case, since the seed groups are updated (seeds-m gets expanded,and seeds-n get destroied), we need to restart the outer while-loop again and continue testing distance between the updated seed groups
    reloopflag = TRUE
    
    # merge seed by "minimaldist" method
    if(seedMergeMethod == "minimaldist") {
      while(reloopflag){
      for(n in 1:length(testList)){
        reloopflag = FALSE
        if(length(testList[[n]])==1 & testList[[n]][1]==-1){
          next
        }
        
        for(m in 1:length(testList)){
          reloopflag = FALSE
          if (m == n){
            next
          }
          
          if (length(testList[[m]])==1 & testList[[m]][1]==-1){
            next
          }
          
          tmpMinDist = 999999999
          for(p in 1:length(testList[[n]])){
            
            lat1 = centroids_pj[testList[[n]][p],"coords.x2"]
            lon1 = centroids_pj[testList[[n]][p],"coords.x1"]
            
            for(q in 1:length(testList[[m]])){
              lat2 = centroids_pj[testList[[m]][q],"coords.x2"]
              lon2 = centroids_pj[testList[[m]][q],"coords.x1"]
              
              dist = sqrt((lat1-lat2)^2+(lon1-lon2)^2)
              if(dist<tmpMinDist){
                tmpMinDist = dist
              }
            }
          }
          
          #if mindist is smaller than threshold, merge m to n, and clear m
          
          if(tmpMinDist < seedMergeDist*1000){
            testList[[n]] = c(testList[[n]], testList[[m]])
            testList[[m]] = c(-1)
            reloopflag = TRUE
            break
          }
          
        }
        if (reloopflag){
          break
        }
      }
    }
    }
    
    # merge seed by "exingravity" method: gravity = population / dist^2, where dist is in km
    if(seedMergeMethod == "exingravity") {
      
      #step1: external gravity calculation for each seed
      #for each seed s', find its neighbour s within 'seedMergeDist' (to be checked if it's necessary) which meets 2 conditions: 
      #(1) pop(s) >= pop(s')
      #(2) gravity(s',s) is the biggest gravity value among s' and its neighbours whose population is higher than s'
      tmpDF = data.frame(orgSeedId=gridUnprj@data[seedFilter,"aggidx"],aggSeedId=-1,inG=-1, exG=-1, ssDist=-1, mergeFlag=FALSE)
      for(i in 1:nrow(tmpDF)){
        maxeG = -1
        aggSeedId = -1
        ssDist = -1
        lat1 = centroids_pj[tmpDF[i, "orgSeedId"], "coords.x2"]
        lon1 = centroids_pj[tmpDF[i, "orgSeedId"], "coords.x1"]
        for(j in 1:nrow(tmpDF)){
          #ignore if i=j
          if( i == j) next
          #ignore if pop(s') > pop(s). if two pop value are equal, still consider merge  
          if(gridUnprj@data[tmpDF[i,"orgSeedId"],gridPopColName] > gridUnprj@data[tmpDF[j,"orgSeedId"],gridPopColName]) next
          
          lat2 = centroids_pj[tmpDF[j, "orgSeedId"], "coords.x2"]
          lon2 = centroids_pj[tmpDF[j, "orgSeedId"], "coords.x1"]
          eucDistSquare = (lat2-lat1)^2 + (lon2-lon1)^2
          
          #ignore if two seeds si and sj are too distant by comparing the educlidean distance between two closest grids attached to each seed. 
          shortestGridsEucDist = 9999999999
          
          # find grids whose aggid equals current seedid (si and sj)
          seed_i_gridFilter = gridUnprj@data[,"aggidx"] == tmpDF[i, "orgSeedId"]
          seed_i_gridIdVec = gridUnprj@data[seed_i_gridFilter, "gridId"]
          
          seed_j_gridFilter = gridUnprj@data[,"aggidx"] == tmpDF[j, "orgSeedId"]
          seed_j_gridIdVec = gridUnprj@data[seed_j_gridFilter, "gridId"]
          
          if(length(seed_i_gridIdVec) > 0 & length(seed_j_gridIdVec) > 0){
            for(m in 1:length(seed_i_gridIdVec)){
              lat_m = centroids_pj[seed_i_gridIdVec[m], "coords.x2"] 
              lon_m = centroids_pj[seed_i_gridIdVec[m], "coords.x1"]
              
              for(n in 1:length(seed_j_gridIdVec)){
                lat_n = centroids_pj[seed_j_gridIdVec[n], "coords.x2"] 
                lon_n = centroids_pj[seed_j_gridIdVec[n], "coords.x1"]
                
                tmpEucDist = sqrt((lat_m-lat_n)^2 + (lon_m-lon_n)^2)
                
                if (shortestGridsEucDist > tmpEucDist) shortestGridsEucDist = tmpEucDist
              }
            }
            # ignore if they are too distant
            if(shortestGridsEucDist > seedMergeDist*1000) next
          } else {
            next
          }
          
          
          
          if (eucDistSquare < 1.0) {
            tmpeG = 999999999
          } else{
            tmpeG = GeoTool.getGravity(massPara=gridUnprj@data[tmpDF[j,"orgSeedId"],gridPopColName], distPara=sqrt(eucDistSquare)/1000)
            #tmpeG = gridUnprj@data[tmpDF[j,"orgSeedId"],gridPopColName] / eucDistSquare * 1000000
          }
          
          if(tmpeG > maxeG){
            maxeG = tmpeG
            aggSeedId = tmpDF[j,"orgSeedId"]
            ssDist = sqrt(eucDistSquare)
          }
        }
        
        tmpDF[i,"aggSeedId"] = aggSeedId
        tmpDF[i,"ssDist"] = ssDist
        tmpDF[i,"exG"] = maxeG
        
      }
      
      #step2: internal gravity calculation for each seed, using all aggregated grids of seed s' to calculate internal gravity
      for(i in 1:nrow(tmpDF)){
        inG = 0.0
        lat1 = centroids_pj[tmpDF[i, "orgSeedId"], "coords.x2"] 
        lon1 = centroids_pj[tmpDF[i, "orgSeedId"], "coords.x1"]
        
        # find all grids whose aggid equals current seedid
        candidateGridFilter = gridUnprj@data[,"aggidx"] == tmpDF[i, "orgSeedId"]
        candidateGridIdVec = gridUnprj@data[candidateGridFilter, "gridId"]
        
        # if there is no grid belongs to this seed
        if(length(candidateGridIdVec) == 0){
          print(sprintf("=== no grid belongs to seed[%i]", tmpDF[i, "orgSeedId"]))
          next
        }
        
        for(j in 1:length(candidateGridIdVec)){
          lat2 = centroids_pj[candidateGridIdVec[j], "coords.x2"] 
          lon2 = centroids_pj[candidateGridIdVec[j], "coords.x1"] 
          eucDist = sqrt((lat2-lat1)^2 + (lon2-lon1)^2)
          
          #if a grid is too close to the seed, igore this grid
          if(eucDist <= gridEdgeLength * 1000) next
          
          #otherwise, sum up the gravity
          inG = inG + GeoTool.getGravity(massPara=gridUnprj@data[candidateGridIdVec[j],gridPopColName], distPara=eucDist/1000)
        }
        
        if(inG > 0){
          tmpDF[i,"inG"] = inG
        }
      }
      
      #step3: update mergeflag
      filter =tmpDF[,"inG"] < tmpDF[,"exG"]
      tmpDF[filter, "mergeFlag"] = TRUE
      tmpDF[!filter, "aggSeedId"] = tmpDF[!filter, "orgSeedId"]
      
      #step4: update aggSeedId: 2->1 4->2 ==> 2->1 4->1
      coreSeedVec = tmpDF[!filter,"aggSeedId"]
      for(i in 1:nrow(tmpDF)){
        
        if(tmpDF[i, "mergeFlag"] == FALSE) next
        
        # if seed (must be newly appended in the following while loop) appears in the orgSeedId column, switch orgSeedId and aggSeedId
        if(tmpDF[i, "orgSeedId"] %in% coreSeedVec){
          tmp = tmpDF[i, "orgSeedId"]
          tmpDF[i, "orgSeedId"] = tmpDF[i, "aggSeedId"]
          tmpDF[i, "aggSeedId"] = tmp
          next
        }
        
        if(tmpDF[i, "aggSeedId"] %in% coreSeedVec){ 
          # find all aggSeedId==orgSeedId records, update their aggSeedId to current orgSeedId's aggSeedId
          orgSeedId = tmpDF[i, "orgSeedId"]
          aggSeedId = tmpDF[i, "aggSeedId"]
          
          tmpfilter = tmpDF[, "aggSeedId"] == orgSeedId
          tmpDF[tmpfilter, "aggSeedId"] = aggSeedId
        } else {
          # in aggSeedId is not a coreSeed, it means there is a path to reach the coreSeed. 
          # e.g. seed->aggseed->parent aggseed-> parent parent aggseed-> coreseed
          continueFlag = TRUE
          traceVec = c(tmpDF[i, "orgSeedId"], tmpDF[i, "aggSeedId"])
          nextId = tmpDF[i, "aggSeedId"]
          while(continueFlag){
            nextId_bak = nextId
            f = tmpDF[, "orgSeedId"] == nextId
            
            nextId = tmpDF[f, "aggSeedId"]
            
            if(nextId %in% traceVec) {
              #if loop seed reference occurs, put it into coreSeedVec and exit loop
              coreSeedVec = c(coreSeedVec, nextId_bak)
              break
            }
            
            if(nextId %in% coreSeedVec){
              continueFlag = FALSE
            }
            
            traceVec = c(traceVec, nextId)
            if(length(traceVec) >= nrow(tmpDF)){
              continueFlag = FALSE
            }
          }
          #print(traceVec)
          
          f = which(tmpDF[,"orgSeedId"] %in% traceVec)
          tmpDF[f, "aggSeedId"] = traceVec[length(traceVec)]
          
        }
      }
      
      #step5: update testList
      uniqueSeedVec = tmpDF[,"aggSeedId"]
      uniqueSeedVec = uniqueSeedVec[!duplicated(uniqueSeedVec)]
      for(i in 1: length(testList)){
        if(testList[[i]] %in% uniqueSeedVec){
          f = tmpDF[,"aggSeedId"]==testList[[i]]
          testList[[i]] = tmpDF[f, "orgSeedId"]
        } else {
          testList[[i]] = c(-1)
        }
      }
      
    }
    aggSeedList = testList
    
    # agglomerate seed
    for (i in 1:length(aggSeedList)){
      
      #skip cleared list element
      if (length(aggSeedList[[i]])==1 & aggSeedList[[i]][1]==-1){
        next
      }
      
      # by default, merge to the smallest idx seed
      aggSeedIdx = min(aggSeedList[[i]])
      
      # or merge to the highest population seed
      if (seedMergeTo == "highestPop") 
      {
        highestPopValue = -1
        for (tmpIdx in aggSeedList[[i]]){
          if (gridUnprj@data[tmpIdx, gridPopColName] > highestPopValue){
            aggSeedIdx = tmpIdx
            highestPopValue = gridUnprj@data[tmpIdx, gridPopColName]
          }
        }
      } else if (seedMergeTo == "highestPopDen")
      { # or merge to the highest population density seed
        highestPopDenValue = -1
        for (tmpIdx in aggSeedList[[i]]){
          if (gridUnprj@data[tmpIdx, gridDenColName] > highestPopDenValue){
            aggSeedIdx = tmpIdx
            highestPopDenValue = gridUnprj@data[tmpIdx, gridDenColName]
          }
        }
      } else if (seedMergeTo == "bboxCentre")
      { # or merge to the geo central seed
        if(length(aggSeedList[[i]]) == 1){#for seed group contains only a single seed, just use the seed
          aggSeedIdx = aggSeedList[[i]][1]
        } else if (length(aggSeedList[[i]]) == 2)
        {#for seed group contains only 2 seeds, just "highestPop" one
          highestPopValue = -1
          for (tmpIdx in aggSeedList[[i]]){
            if (gridUnprj@data[tmpIdx, gridPopColName] > highestPopValue){
              aggSeedIdx = tmpIdx
              highestPopValue = gridUnprj@data[tmpIdx, gridPopColName]
            }
          }
        } else {#for seed group contains more than 2 seeds, find the central one
          minx1 = min(centroids_pj[aggSeedList[[i]],"coords.x1"])
          maxx1 = max(centroids_pj[aggSeedList[[i]],"coords.x1"])
          minx2 = min(centroids_pj[aggSeedList[[i]],"coords.x2"])
          maxx2 = max(centroids_pj[aggSeedList[[i]],"coords.x2"])
          centralx1 = (minx1 + maxx1)/2
          centralx2 = (minx2 + maxx2)/2
          minAbsDist = 99999999
          for (tmpIdx in aggSeedList[[i]]){
            tmpAbsDist = abs(centralx1 - centroids_pj[tmpIdx,"coords.x1"]) + abs(centralx2 - centroids_pj[tmpIdx,"coords.x2"])
            if (tmpAbsDist < minAbsDist){
              aggSeedIdx = tmpIdx
              minAbsDist = tmpAbsDist
            }
          }
        }
      } 
      #print(sprintf("%i: %i", i, aggSeedIdx))
      vec = aggSeedList[[i]]
      
      if (length(vec) == 1) next
      
      vec = vec[which(vec!=aggSeedIdx)]
      for(x in 1:length(vec)){
        f = gridUnprj@data[,"aggidx"] == vec[x]
        gridUnprj@data[f,"aggidx2"] = gridUnprj@data[aggSeedIdx,"aggidx2"]        
      }

    }
  }
  # mark isseed2 column
  aggSeedIdxVec = gridUnprj@data[,"aggidx2"]
  aggSeedIdxVec = aggSeedIdxVec[!duplicated(aggSeedIdxVec) & (aggSeedIdxVec > 0)]
  gridUnprj@data[aggSeedIdxVec,"isseed2"] = 1
  aggSeedFilter = gridUnprj@data[,"isseed2"] == 1
  
  # then we need update aggidx2 in the gridUnprj@data
  # identify all aggregated seed
  filter = gridUnprj@data[ ,"aggidx"] != gridUnprj@data[ ,"aggidx2"]
  filter = filter & seedFilter
  aggSeedDF = gridUnprj@data[filter ,c("aggidx","aggidx2")]
  # replace aggidx2 
  for(i in 1:nrow(aggSeedDF)){
    f = gridUnprj@data[,"aggidx"] == aggSeedDF[i, "aggidx"]
    gridUnprj@data[f,"aggidx2"] = aggSeedDF[i, "aggidx2"]
  }
  
  
  # calc AI based on seed
  rltDataFrame = data.frame(seedIdx=NULL,AI=NULL,sumPop=NULL, sumArea=NULL)
  df = gridUnprj@data[seedFilter,]
  for (i in 1:nrow(df)){
    seedIdx = df[i, "gridId"] #attr(df[i,], "row.names")
    filter = gridUnprj@data[, "aggidx"] == seedIdx
    sumPop = sum(gridUnprj@data[filter, gridPopColName])
    sumArea =  nrow(gridUnprj@data[filter, ]) / nrow(gridUnprj@data)
    AI = sumPop / sum(gridUnprj@data[, gridPopColName])
    rltDataFrame<-rbind(rltDataFrame,data.frame(seedIdx=seedIdx, AI=AI, sumPop=sumPop, sumArea=sumArea))
  }
  #rltDataFrame$AI = format(rltDataFrame$AI, nsmall=4, digits=4, scientific = FALSE)
  write.table(rltDataFrame, file=sprintf("%s/AI_%i_%i_%i_%s_%s_orgseed.csv", outShpFileDir, thPopDen, thSeedMinPop, thTvlTime, seedMergeMethod, equationType), row.names = FALSE, sep=",")
  
  
  # calc AI based on seed2 (agglomerated seed)
  rltDataFrame = data.frame(seedIdx=NULL,AI=NULL,sumPop=NULL, sumArea=NULL)
  df = gridUnprj@data[aggSeedFilter,]
  for (i in 1:nrow(df)){
    seedIdx = df[i, "gridId"] 
    filter = gridUnprj@data[, "aggidx2"] == seedIdx    
    sumPop = sum(gridUnprj@data[filter, gridPopColName])
    sumArea =  nrow(gridUnprj@data[filter, ]) / nrow(gridUnprj@data)
    AI = sumPop / sum(gridUnprj@data[, gridPopColName])
    rltDataFrame<-rbind(rltDataFrame,data.frame(seedIdx=seedIdx, AI=AI, sumPop=sumPop, sumArea=sumArea))
  }
  
  #rltDataFrame$AI = format(rltDataFrame$AI, nsmall=4, digits=4, scientific = FALSE)
  write.table(rltDataFrame, file=sprintf("%s/AI_%i_%i_%i_%s_%s_aggseed.csv", outShpFileDir, thPopDen, thSeedMinPop, thTvlTime, seedMergeMethod, equationType), row.names = FALSE, sep=",")

  writeOGR(obj=gridUnprj, dsn=outShpFileDir, layer=sprintf("AI_%i_%i_%i_%s_%s", thPopDen, thSeedMinPop, thTvlTime, seedMergeMethod, equationType), driver="ESRI Shapefile", check_exists=TRUE, overwrite_layer=TRUE)
  
  algEndTime = Sys.time()
  
  print(sprintf("==========> all done (in %.2f seconds) <==========", as.numeric(algEndTime-algStartTime, units="secs")))
}


AI.batch <- function(vecThPopDen=c(150, 300, 500), 
                     vecThSeedMinPop=c(20000, 50000, 100000),
                     vecThTvlTime=c(60, 90)
){
  # # # # # # # # # # # # # # # # # # # # # # # # # # # #
  # This is a shortcut to run AI.gen over multiple threshold combinations. The input pareameters listed here are all keys to affect final outputs. 
  # The rest parameters required by AI.gen are left as default values. If we want to adjust only one of them for the AI.batch call, say changing "thSearchSeedRadius" from 200 to 250,
  # we need to change its default value in the AI.gen function definition, and reload the entire script then call AI.batch again. 
  # Input parameters:
  # (1) vecThPopDen: an integer vector of population density thresholds 
  # (2) vecThSeedMinPop: an integer vector of minimum seed population thresholds
  # ATTENTION: if additional seed file is NOT provided, the seed will directly be selected from population grids, which generally contain smaller population values than provided by the seed file. Make sure to adjust 'ThSeedMinPop' to fit different options
  # (3) vecThTvlTime: an integer vector of travel time thresholds
  # Output:
  # (1) outputs of AI.gen for each combination
  # # # # # # # # # # # # # # # # # # # # # # # # # # # #
  sTime = Sys.time()
  
  for (ThPopDen in vecThPopDen){
    for (ThSeedMinPop in vecThSeedMinPop){
      for (ThTvlTime in vecThTvlTime){
        print(sprintf("============== BATCH RUN: (%i,%i,%i) ==============", ThPopDen, ThSeedMinPop, ThTvlTime))
        
        AI.gen(thPopDen=ThPopDen, 
               thSeedMinPop=ThSeedMinPop, 
               thTvlTime=ThTvlTime)
      }
    }
  }
  
  eTime = Sys.time()
  print("==============================================")
  print(sprintf("=== BATCH DONE (in %.2f seconds) ===", as.numeric(eTime-sTime, units="secs")))
  print("==============================================")
}


AI.sum <- function(vecThPopDen=c(150, 300, 500), 
                   vecThSeedMinPop=c(20000, 50000, 100000),
                   vecThTvlTime=c(60, 90),
                   outDir=gOutRootDir,
                   methodDir="genAI",
                   seedDirName="ByTopPop",
                   seedMergeMethod="exingravity",
                   equationType = "SQUAREDDIST",
                   countryName = gCountryName,
                   dataYear = gDataYear){
  # # # # # # # # # # # # # # # # # # # # # # # # # # # #
  # Input parameters:
  # (1) vecThPopDen: an integer vector of population density thresholds 
  # (2) vecThSeedMinPop: an integer vector of minimum seed population thresholds
  # (3) vecThTvlTime: an integer vector of travel time thresholds
  # (4) outDir: the root dir of outputs
  # (5) methodDir: if seed file is provided, set to "genAI"; otherwise, set to "genAI_2"
  # (6) seedDirName: the specific output dir name for different seed selections
  # (7) seedMergeMethod: "exingravity" or "minimaldist"
  # (8) countryName: the country name of dataset
  # (9) dataYear: the year of dataset
  # Output:
  # (1) create a table contains summed AI values of every combination (vecThPopDen X vecThSeedMinPop X vecThTvlTime)
  # # # # # # # # # # # # # # # # # # # # # # # # # # # #
  
  rltDF <- data.frame(thpopden=NULL, thseedminpop=NULL, thtvltime=NULL, ttlAI=NULL)
  for (ThPopDen in vecThPopDen){
    for (ThSeedMinPop in vecThSeedMinPop){
      for (ThTvlTime in vecThTvlTime){
        filePath = sprintf("%s%s/%s/%s/%s/AI_%i_%i_%i_%s_%s_aggseed.csv", outDir, countryName, methodDir, dataYear, seedDirName, ThPopDen, ThSeedMinPop, ThTvlTime, seedMergeMethod, equationType)
        #print(filePath)
        if (file.exists(filePath)){
          tmpDF <- read.table(filePath, header=TRUE, sep=",", blank.lines.skip = TRUE, fill = TRUE)
          ttlAI = sum(tmpDF[,"AI"])
          ttlPop = sum(tmpDF[,"sumPop"])
          
          ttlArea = sum(tmpDF[,"sumArea"])
          rltDF <- rbind(rltDF, data.frame(thpopden=ThPopDen, thseedminpop=ThSeedMinPop, thtvltime=ThTvlTime, ttlAI=ttlAI, ttlPop=ttlPop, ttlArea=ttlArea))
        }
      }
    }
  }
  if (nrow(rltDF) == 0) {
    print("=====no valid data (*seed.csv) found in target folder")
  } else {
    rltDF$ttlAI = format(rltDF$ttlAI, nsmall=4, digits=4, scientific = FALSE)
    rltDF$thseedminpop = format(rltDF$thseedminpop, scientific = FALSE)
    write.table(rltDF, file=sprintf("%s%s/%s/%s/%s/sumAI_%s_%s.csv", outDir, countryName, methodDir, dataYear, seedDirName, seedMergeMethod, equationType), row.names = FALSE, sep=",", quote = FALSE)
    print("=====done")
  }
}
