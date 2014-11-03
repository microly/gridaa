======== User Manual ========
This tool generates urbanization agglomeration indice using CIESIN population grid data.


== PART 1: Dataset Preparation ==  

(1) This tool mainly relies on the population data from CIESIN website: http://sedac.ciesin.columbia.edu/data/set/gpw-v3-population-density/data-download
To download the population grid for a country, please follow the steps below:
(a) in "Geography", choose "Country", then select your interested country
(b) in "Data Set", choose "Population Density Grid"
(c) in "Data Attributes", choose "grid"-"2.5'"-"1990,1995,2000"
Then click "download" button. The downloaded zip file contains 3 years population data, go for the "readme_pdens_grid_prod.txt" file first to understand how the data is organized. 
The population grid data is in ArcGIS grid (raster) format, user needs to convert it into vector format (shapefile) in ArcGIS.

(2) Optionally, user can provide "seed" files to facilitate the agglomeration algorithm. The seed data can based on GRUMP settlement points, which is accessible from this link
http://sedac.ciesin.columbia.edu/data/set/grump-v1-settlement-points/data-download
To download the settlement points for a country, please follow the steps below:
(a) in "Geography", choose "Country", then select your interested country
(b) in "Data Set", choose "Settlement Points"
(c) in "Data Attributes", choose ".shp"-"circa 2000"
Then click "download" button. The downloaded zip file contains the settlement data in shape file, go for the "readme.txt" file first to understand the data structure. 

== PART 2: How It Works ==

Each agglomeration needs a seed. User can prepare a seed file for the algorithm or simply choose top N population grid as seeds. In either way, the selected seeds must meet a user defined seed minimum population criterion.

For each non-seed district, the algorithm first finds its "closest" seed using the following gravity equation:
gravity = seedpop / (dist^2)
where "seedpop" represents the population of a seed and "dist" stands for the Euclidian distance between the centroids of seed and non-seed districts.
A seed is more "attractive" to a non-seed if the gravity value is higher. In this way, the seed with the highest gravity value is assigned to that non-seed. 
But this doesn't indicate that this non-seed district can actually be merged to the seed. To make a merging decision, the algorithm takes into account two more factors:
(1) the non-seed district has a big enough population to meet a user defined minimum population criterion
(2) the travel time between the centroids of seed and non-seed districts meets a user defined maximum travel time criterion.
If the travel time between a seed and non-seed cannot be found in the cached route database (i.e. "output/countryname/routefinfo/db.csv"), the algorithm will call Mapquest/Google navigation API to get this value and then cache it. 
This will boost the processing speed dramatically in the next run.

Merging Seed Agglomerations
The algorithm provides two options for merging seed agglomerations:
(1) using "minimaldist" option, which relies on a user defined "seedMergeDist" threshold. If the Euclidian distance between two seeds is less than this threshold value, their agglomerations will be merged.
(2) using "exingravity" option, which determines the merging by considering the external and internal gravity factors, read the "change log" part of source code for more details.


== PART 3: How To Use It == 

The algorithm is written in R and tested in Mac OS X 10.8.5. User is assumed to know how to use R.

Before loading the script into R console, some changes need to be made in the source code:
(1) Set up your working directory
setwd("/Users/yiqunc/CIESINAI")
(2) Set up global variables:
the outputs for a country in a specific year will be stored at "gOutRootDirgCountryName/gDataYear/seedDirName" 
gOutRootDir <<- "./output/"
gCountryName <<- "Sirilanka"
gDataYear <<- "2012"

if travel distance / euclidean distance is bigger than gTERMax, the API results are treated as issused ones and need further correction.
gTERMax <<- 3.0

show debug infomation when processing
gShowDebugInfo = FALSE
(3) Define a projected srs (spatial reference system) for your case study area. User can use the "Proj4js format" string declared in http://spatialreference.org/ 
Finding a proper projected srs is important it affects the accuracy of euclidean distance calculation.
User can easily extend the srsDF data frame to include new srs for the target country.
If user cannot provide an valid projected srs, the script will use EPSG:3857 as the universal projected srs (http://trac.osgeo.org/proj/wiki/FAQ). While, this is NOT the best solution for any particular area.

(4) Setup default parameter values for generic function "AI.gen". Please check out the source code for parameter definitions. Here are some usage examples:

(a) create AI with single threshold combination: population density:150, minimum seed population 20000, travel time 60 minutes
AI.gen(thPopDen=150,thSeedMinPop=20000, thTvlTime=60)

(b) run AI in batch mode
AI.batch(vecThPopDen=c(150, 300),vecThSeedMinPop=c(50000, 100000),vecThTvlTime=c(60, 90))

(c) calculate sum AI for the batch mode outputs
AI.sum(vecThPopDen=c(150, 300),vecThSeedMinPop=c(50000, 100000))

