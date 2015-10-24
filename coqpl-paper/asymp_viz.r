library(functional)
library(ggplot2)
library(tikzDevice)

tikz('asymp_viz.tex', standAlone = FALSE)
dev.new(height=5,width=8)
par(mar = c(1,2,1,1))


xrang <- c(0,4)
yrang <- c(-5,5)

plot.new()

plot.window(xlim=xrang, ylim=yrang,
            xaxs="i", yaxs="i",
                                        #            width=3,height=3
            )
par(mar=c(0,0,0,0))

title(xlab="time", ylab="",                 # axis labels
      )


## axis(1,                                 # x axis
##      pos=0,                             # at y=0
##      ## at=xrang,                          # where to put labels (+ extend the line)
##      ## labels=F,                          # don't show x axis
##      ## tck=0,
##      )

axis(2,                                 # y axis
     pos=0,                             # at x=0
     ## at=c(-4,0,4),
     ## lab=c("",0,""),
     ## tck=0,
     xaxs="i", yaxs="i"
     )

abline(h=3, col = "red")
abline(h=-3, col = "red")

## ## Draw some random points
set.seed(467)

startT <- 0
startX <- 1

ctrlRuns <- runif(10, 0, 4)

                                        #set.seed(239)
pickRand <- function(t) { runif(1,-3,3) }
ctrlRunVals <- lapply(ctrlRuns, pickRand)

xs <- append(ctrlRuns, startT)
ys <- unlist(append(ctrlRunVals,startX))

                                        # "zip" and sort so the lines connect properly
data <- data.frame(x = xs, y = ys)
data <- data[order(data$x), ]

                                        # draw lines
lines(data)
points(xs,ys,
       pch=4,                            # point char 4 is 'x'
       )


                                        # close tikz generation
dev.off()
