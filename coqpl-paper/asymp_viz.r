library(functional)
require(tikzDevice)

tikz('asymp_viz.tex', standAlone = FALSE, width = 5,height = 5)


xrang <- c(0,4)
yrang <- c(-5,5)

plot.new()

plot.window(xlim=xrang, ylim=yrang,
            xlab="", ylab="",                 # axis labels
            )
#frame()


axis(1,                                 # x axis
     pos=0,                             # at y=0
     ## at=xrang,                          # where to put labels (+ extend the line)
     ## labels=F,                          # don't show x axis
     ## tck=0,
     )

axis(2,                                 # y axis
     pos=0,                             # at x=0
     ## at=c(-4,0,4),
     ## lab=c("",0,""),
     ## tck=0,
     )

abline(h=3,                                # the func
       untf = FALSE,
       col = "red"
       )

abline(h=-3,                                # the func
       untf = FALSE,
       col = "red"
       )

## ## Draw some random points
set.seed(114)

startT <- 0.1
startX <- 2.5

# vals of e and ne at time t
getBounds <- function(t) { list(u = 3, l = -3) }

ctrlRuns <- runif(8, 0, 4)
#ctrlRuns <- c(1.260825, 0.587869, 3.509754, 2.328480)
ctrlBounds <- lapply(ctrlRuns, getBounds)

set.seed(123)
pickRand <- function(ls) { runif(1,ls$l,ls$u) }
ctrlRunVals <- lapply(ctrlBounds, pickRand)


xs <- append(ctrlRuns, startT)
ys <- unlist(append(ctrlRunVals,startX))

# "zip" and sort so the lines connect properly
data <- data.frame(x = xs, y = ys)
data <- data[order(data$x), ]

# draw lines
lines(data)


# close tikz generation
dev.off()
