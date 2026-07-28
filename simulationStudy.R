## Subject: Simulations for 'Semi-Parametric Confidence Intervals via the Pivotal Method'
## Author: Benjamin L. Jacobs <bjacobs1@iastate.edu>
## Date: 10.9.2025
## Last update: 6.29.2026

set.seed(6459299)
setwd('filepath') # set your working directory here

S.global <- 5000 # number of data sets in each simulation, for the paper will be 5000
M.global <- 10000 # number of simulations used to approximate cd's, for the paper will be 10000
a.global <- 100000 # intercept for simulations 1, 3, and 4, for the paper will be 100000. The point of such a large intercept is to verify 
# that my methods correctly cancel out the intercept. If they do not, then larger intercepts will have more noticeable effects on the coverage rates.

## function to generate samples from the semi-parametric confidence distribution
## inputs: 
# y: response vector
# x: the covariate vector
# M: number of samples to draw
# case: numeric, 1 through 4, which application from the paper to follow when calculating the CI
## outputs:
# beta.cd: a vector of draws from the cd for beta
# reject.count: an integer, the number of rejected permutations/sign-switchings
semipar.cd <- function(y,x=NULL,M=999,case=1){
  
  # set up the lambda and x vectors
  if(case==1){
    lambda <- x-mean(x)
  }else if(case==2){
    lambda <- rep(1,length(y))
    x <- rep(1,length(y))
  }else if(case==3){
    xo <- order(x)
    x <- x[xo]
    y <- y[xo]
    if(length(y) %% 2 == 0){
      lambda <- rep(c(-1,1),each=length(y)/2)
    }else{
      lambda <- c(-2,rep(-1,length(y)/2-1),rep(1,length(y)/2+1))
    }
  }else if(case==3.1){ # centered ranks. this does not appear on the poster, but may appear in my paper
    xo <- order(x)
    x <- x[xo]-mean(x)
    y <- y[xo]
    lambda <- rank(x,ties.method="random")-mean(rank(x,ties.method="random"))
  }
  
  # generate M successful random matrices and record the number of failures
  fails <- 0
  beta.cd <- rep(NA,M)
  for(m in 1:M){
    
    cond <- F
    while(!cond){
      if(case==1){
        R <- diag(length(y))[sample(1:length(y)),]
      }else if(case==2){
        R <- diag(sample(c(-1,1),size=length(y),replace=T)  )
      }else if(case==3){
        if(length(y) %% 2 == 0){
          R0 <- sample( c(-1,1), size=length(y)/2, replace=T )
          R <- diag( c(R0,sample(R0)) )
        }else{
          R.lower <- sample(c(-1,1),size=length(y)/2,replace=T)
          R <- diag(  c(R.lower,sample(c(R.lower,R.lower[1])))  )
        }
      }else if(case==3.1){
        if(length(y) %% 2 == 0){
          R0 <- sample( c(-1,1), size=length(y)/2, replace=T )
          R <- diag( c(R0,rev(R0)) )
        }else{
          R0 <- sample(c(-1,1),size=length(y)/2,replace=T)
          R <- diag(  c(R0,1,rev(R0))  )
        }
      }
      cond <- lambda%*%x != lambda%*%R%*%x
      fails <- fails + !cond
    }
    
    beta.cd[m] <- (lambda%*%y - lambda%*%R%*%y)/(lambda%*%x - lambda%*%R%*%x)
    
  }
  return(list(beta.cd=beta.cd,reject.count=fails))
}

# draws from the percentile residual bootstrap cd
## inputs:
# y: the response vector
# x: the covariate vector
# M:: the number of draws from the CD to produce
## ouput:
# beta.cd: the vector of draws from the CD
resid.bootstrap <- function(y,x,M){
  tmp <- lm(y~x)
  e <- resid(tmp)
  beta.cd <- rep(NA,M)
  for(m in 1:M){
    y.tmp <- fitted(tmp)+sample(e,replace=T)
    beta.cd[m] <- sum( (y.tmp-mean(y.tmp))*(x-mean(x)) )/sum( (x-mean(x))^2 )
  }
  return(2*coef(tmp)[2]-beta.cd)
}

# draws from the percentile wild bootstrap cd
## inputs:
# y: the response vector
# x: the covariate vector
# M:: the number of draws from the CD to produce
## ouput:
# beta.cd: the vector of draws from the CD
wild.bootstrap <- function(y,x,M){
  tmp <- lm(y~x)
  e <- resid(tmp)
  beta.cd <- rep(NA,M)
  for(m in 1:M){
    y.tmp <- fitted(tmp)+sample(c(-1,1),size=length(y),replace=T)*e
    beta.cd[m] <- sum( (y.tmp-mean(y.tmp))*(x-mean(x)) )/sum( (x-mean(x))^2 )
  }
  return(beta.cd)
}

# median bootstrap:
# draws from the basic bootstrap confidence distribution for the population median
med.bootstrap <- function(y,M){
  
  beta.cd <- rep(NA,M)
  for(m in 1:M){
    beta.cd[m] <- median(sample(y,replace=T))
  }
  return(2*median(y)-beta.cd)
}

###### simulation study 1 ######### 
## Simple Linear Regression
## inputs: 
# n: an integer, the sample size
# S: an integer, the number of data sets to simulate
## ouputs:
sim1 <- function(n,S=S.global){
  
  w80 <- rep(NA,S)
  c80 <- rep(NA,S)
  w90 <- rep(NA,S)
  c90 <- rep(NA,S)
  w95 <- rep(NA,S)
  c95 <- rep(NA,S)
  cdf <- rep(NA,S)
  rej <- rep(NA,S)
  
  w80.b <- rep(NA,S)
  c80.b <- rep(NA,S)
  w90.b <- rep(NA,S)
  c90.b <- rep(NA,S)
  w95.b <- rep(NA,S)
  c95.b <- rep(NA,S)
  cdf.b <- rep(NA,S)
  
  w80.n <- rep(NA,S)
  c80.n <- rep(NA,S)
  w90.n <- rep(NA,S)
  c90.n <- rep(NA,S)
  w95.n <- rep(NA,S)
  c95.n <- rep(NA,S)
  cdf.n <- rep(NA,S)
  
  scales <- rep(NA,S)
  slopes <- rep(NA,S)
  
  for(s in 1:S){
    sig <- abs(rcauchy(n=1))
    e <- abs(rcauchy(n=n,scale=sig))
    slope <- rcauchy(n=1)
    y <- a.global+slope*(1:n)+e
    tmp <- semipar.cd(y=y,x=1:n,M=M.global,case=1)
    qs <- quantile(x=tmp$beta.cd,c(.025,.05,.1,.9,.95,.975))
    w80[s] <- diff(qs[c(3,4)])
    c80[s] <- slope >= qs[3] & slope <= qs[4]
    w90[s] <- diff(qs[c(2,5)])
    c90[s] <- slope >= qs[2] & slope <= qs[5]
    w95[s] <- diff(qs[c(1,6)])
    c95[s] <- slope >= qs[1] & slope <= qs[6]
    cdf[s] <- mean( tmp$beta.cd <= slope)
    rej[s] <- tmp$reject.count
    
    tmp2 <- resid.bootstrap(y=y,x=1:n,M=M.global)
    qs <- quantile(x=tmp2,c(.025,.05,.1,.9,.95,.975))
    w80.b[s] <- diff(qs[c(3,4)])
    c80.b[s] <- slope >= qs[3] & slope <= qs[4]
    w90.b[s] <- diff(qs[c(2,5)])
    c90.b[s] <- slope >= qs[2] & slope <= qs[5]
    w95.b[s] <- diff(qs[c(1,6)])
    c95.b[s] <- slope >= qs[1] & slope <= qs[6]
    cdf.b[s] <- mean( tmp2 <= slope)
    
    tmp <- lm(y~I(1:n))
    tmp1 <- confint(tmp,level=.8)[2,]
    tmp2 <- confint(tmp,level=.9)[2,]
    tmp3 <- confint(tmp,level=.95)[2,]
    qs <- c(tmp3[1],tmp2[1],tmp1[1],tmp1[2],tmp2[2],tmp3[2])
    w80.n[s] <- diff(qs[c(3,4)])
    c80.n[s] <- slope >= qs[3] & slope <= qs[4]
    w90.n[s] <- diff(qs[c(2,5)])
    c90.n[s] <- slope >= qs[2] & slope <= qs[5]
    w95.n[s] <- diff(qs[c(1,6)])
    c95.n[s] <- slope >= qs[1] & slope <= qs[6]
    cdf.n[s] <- pt(q=(summary(tmp)$coefficients[2,1]-slope)/summary(tmp)$coefficients[2,2],
                   df=summary(tmp)$df[2]
    )
    
    slopes[s] <- slope
    scales[s] <- sig
    
    if(s %% 25 == 0){print(s)}
  }
  return(list(w80=w80,w90=w90,w95=w95,cdf=cdf,rej=rej,
              c80=c80,c90=c90,c95=c95,cdf=cdf,
              c80.b=c80.b,c90.b=c90.b,c95.b=c95.b,
              w80.b=w80.b,w90.b=w90.b,w95.b=w95.b,cdf.b=cdf.b,
              c80.n=c80.n,c90.n=c90.n,c95.n=c95.n,
              w80.n=w80.n,w90.n=w90.n,w95.n=w95.n,cdf.n=cdf.n,
              slopes=slopes,scales=scales
              ))
}

s1 <- sim1(n=10)
s1.1 <- sim1(n=30)
s1.2 <- sim1(n=50)


####### Simulation Study 2 #####
## Median of Cauchy distribution
sim2 <- function(n,S=S.global){
  
  w80 <- rep(NA,S)
  c80 <- rep(NA,S)
  w90 <- rep(NA,S)
  c90 <- rep(NA,S)
  w95 <- rep(NA,S)
  c95 <- rep(NA,S)
  cdf <- rep(NA,S)
  rej <- rep(NA,S)
  
  w80.b <- rep(NA,S)
  c80.b <- rep(NA,S)
  w90.b <- rep(NA,S)
  c90.b <- rep(NA,S)
  w95.b <- rep(NA,S)
  c95.b <- rep(NA,S)
  cdf.b <- rep(NA,S)
  
  w80.n <- rep(NA,S)
  c80.n <- rep(NA,S)
  w90.n <- rep(NA,S)
  c90.n <- rep(NA,S)
  w95.n <- rep(NA,S)
  c95.n <- rep(NA,S)
  cdf.n <- rep(NA,S)
  
  scales <- rep(NA,S)
  slopes <- rep(NA,S)
  
  for(s in 1:S){
    sig <- abs(rcauchy(n=1))
    e <- rcauchy(n=n,scale=sig)
    slope <- rcauchy(n=1)
    y <- 0+slope+e
    tmp <- semipar.cd(y=y,x=rep(1,n),M=M.global,case=2)
    qs <- quantile(x=tmp$beta.cd,c(.025,.05,.1,.9,.95,.975))
    w80[s] <- diff(qs[c(3,4)])
    c80[s] <- slope >= qs[3] & slope <= qs[4]
    w90[s] <- diff(qs[c(2,5)])
    c90[s] <- slope >= qs[2] & slope <= qs[5]
    w95[s] <- diff(qs[c(1,6)])
    c95[s] <- slope >= qs[1] & slope <= qs[6]
    cdf[s] <- mean( tmp$beta.cd <= slope)
    rej[s] <- tmp$reject.count
    
    tmp2 <- med.bootstrap(y=y,M=M.global)
    qs <- quantile(x=tmp2,c(.025,.05,.1,.9,.95,.975))
    w80.b[s] <- diff(qs[c(3,4)])
    c80.b[s] <- slope >= qs[3] & slope <= qs[4]
    w90.b[s] <- diff(qs[c(2,5)])
    c90.b[s] <- slope >= qs[2] & slope <= qs[5]
    w95.b[s] <- diff(qs[c(1,6)])
    c95.b[s] <- slope >= qs[1] & slope <= qs[6]
    cdf.b[s] <- mean( tmp2 <= slope)
    
    tmp1 <- t.test(y,conf.level=.8)$conf.int
    tmp2 <- t.test(y,conf.level=.9)$conf.int
    tmp3 <- t.test(y,conf.level=.95)$conf.int
    qs <- c(tmp3[1],tmp2[1],tmp1[1],tmp1[2],tmp2[2],tmp3[2])
    w80.n[s] <- diff(qs[c(3,4)])
    c80.n[s] <- slope >= qs[3] & slope <= qs[4]
    w90.n[s] <- diff(qs[c(2,5)])
    c90.n[s] <- slope >= qs[2] & slope <= qs[5]
    w95.n[s] <- diff(qs[c(1,6)])
    c95.n[s] <- slope >= qs[1] & slope <= qs[6]
    cdf.n[s] <- t.test(y,mu=slope)$p.value
    
    slopes[s] <- slope
    scales[s] <- sig
    
    if(s %% 25 == 0){print(s)}
  }
  return(list(w80=w80,w90=w90,w95=w95,cdf=cdf,rej=rej,
              c80=c80,c90=c90,c95=c95,cdf=cdf,
              c80.b=c80.b,c90.b=c90.b,c95.b=c95.b,
              w80.b=w80.b,w90.b=w90.b,w95.b=w95.b,cdf.b=cdf.b,
              c80.n=c80.n,c90.n=c90.n,c95.n=c95.n,
              w80.n=w80.n,w90.n=w90.n,w95.n=w95.n,cdf.n=cdf.n,
              slopes=slopes,scales=scales
              ))
}
s2 <- sim2(n=10)
s2.1 <- sim2(n=30)
s2.2 <- sim2(n=50)


####### Simulation Study 3 #######
## Heteroskedastic regression
# Cauchy errors
sim3 <- function(n,S=S.global){
  
  w80 <- rep(NA,S)
  c80 <- rep(NA,S)
  w90 <- rep(NA,S)
  c90 <- rep(NA,S)
  w95 <- rep(NA,S)
  c95 <- rep(NA,S)
  cdf <- rep(NA,S)
  rej <- rep(NA,S)
  
  w80.b <- rep(NA,S)
  c80.b <- rep(NA,S)
  w90.b <- rep(NA,S)
  c90.b <- rep(NA,S)
  w95.b <- rep(NA,S)
  c95.b <- rep(NA,S)
  cdf.b <- rep(NA,S)
  
  w80.cr <- rep(NA,S)
  c80.cr <- rep(NA,S)
  w90.cr <- rep(NA,S)
  c90.cr <- rep(NA,S)
  w95.cr <- rep(NA,S)
  c95.cr <- rep(NA,S)
  cdf.cr <- rep(NA,S)
  rej.cr <- rep(NA,S)
  
  w80.n <- rep(NA,S)
  c80.n <- rep(NA,S)
  w90.n <- rep(NA,S)
  c90.n <- rep(NA,S)
  w95.n <- rep(NA,S)
  c95.n <- rep(NA,S)
  cdf.n <- rep(NA,S)
  
  scales <- rep(NA,S)
  slopes <- rep(NA,S)
  
  for(s in 1:S){
    sig <- abs(rcauchy(n=1))
    x <- runif(n)*10
    e <- rcauchy(n=n,scale=sig*x) #rnorm(n=n,sd=2*sqrt(n))
    slope <- rcauchy(1)
    y <- a.global+slope*x+e
    
    tmp <- semipar.cd(y=y,x=x,M=M.global,case=3)
    qs <- quantile(x=tmp$beta.cd,c(.025,.05,.1,.9,.95,.975))
    w80[s] <- diff(qs[c(3,4)])
    c80[s] <- slope >= qs[3] & slope <= qs[4]
    w90[s] <- diff(qs[c(2,5)])
    c90[s] <- slope >= qs[2] & slope <= qs[5]
    w95[s] <- diff(qs[c(1,6)])
    c95[s] <- slope >= qs[1] & slope <= qs[6]
    cdf[s] <- mean( tmp$beta.cd <= slope)
    rej[s] <- tmp$reject.count
    
    tmp2 <- semipar.cd(y=y,x=x,M=M.global,case=3.1)
    qs <- quantile(x=tmp2$beta.cd ,c(.025,.05,.1,.9,.95,.975))
    w80.cr[s] <- diff(qs[c(3,4)])
    c80.cr[s] <- slope >= qs[3] & slope <= qs[4]
    w90.cr[s] <- diff(qs[c(2,5)])
    c90.cr[s] <- slope >= qs[2] & slope <= qs[5]
    w95.cr[s] <- diff(qs[c(1,6)])
    c95.cr[s] <- slope >= qs[1] & slope <= qs[6]
    cdf.cr[s] <- mean( tmp2$beta.cd <= slope)
    rej.cr[s] <- tmp2$reject.count
    
    tmp2 <- wild.bootstrap(y=y,x=x,M=M.global)
    qs <- quantile(x=tmp2,c(.025,.05,.1,.9,.95,.975))
    w80.b[s] <- diff(qs[c(3,4)])
    c80.b[s] <- slope >= qs[3] & slope <= qs[4]
    w90.b[s] <- diff(qs[c(2,5)])
    c90.b[s] <- slope >= qs[2] & slope <= qs[5]
    w95.b[s] <- diff(qs[c(1,6)])
    c95.b[s] <- slope >= qs[1] & slope <= qs[6]
    cdf.b[s] <- mean( tmp2 <= slope)
    
    tmp <- lm(y~x)
    tmp1 <- confint(tmp,level=.8)[2,]
    tmp2 <- confint(tmp,level=.9)[2,]
    tmp3 <- confint(tmp,level=.95)[2,]
    qs <- c(tmp3[1],tmp2[1],tmp1[1],tmp1[2],tmp2[2],tmp3[2])
    w80.n[s] <- diff(qs[c(3,4)])
    c80.n[s] <- slope >= qs[3] & slope <= qs[4]
    w90.n[s] <- diff(qs[c(2,5)])
    c90.n[s] <- slope >= qs[2] & slope <= qs[5]
    w95.n[s] <- diff(qs[c(1,6)])
    c95.n[s] <- slope >= qs[1] & slope <= qs[6]
    cdf.n[s] <- pt(q=(summary(tmp)$coefficients[2,1]-slope)/summary(tmp)$coefficients[2,2],
                   df=summary(tmp)$df[2]
                   )
    
    slopes[s] <- slope
    scales[s] <- sig
    
    if(s %% 25 == 0){print(s)}
  }
  return(list(w80=w80,w90=w90,w95=w95,cdf=cdf,rej=rej,
              c80=c80,c90=c90,c95=c95,cdf=cdf,
              c80.cr=c80.cr,c90.cr=c90.cr,c95.cr=c95.cr,rej.cr=rej.cr,
              w80.cr=w80.cr,w90.cr=w90.cr,w95.cr=w95.cr,cdf.cr=cdf.cr,
              c80.b=c80.b,c90.b=c90.b,c95.b=c95.b,
              w80.b=w80.b,w90.b=w90.b,w95.b=w95.b,cdf.b=cdf.b,
              c80.n=c80.n,c90.n=c90.n,c95.n=c95.n,
              w80.n=w80.n,w90.n=w90.n,w95.n=w95.n,cdf.n=cdf.n,
              slopes=slopes,scales=scales
              ))
}

s3 <- sim3(n=10)
s3.1 <- sim3(n=30)
s3.2 <- sim3(n=50)




save(s1,s1.1,s1.2,s2,s2.1,s2.2,s3,s3.1,s3.2,
     file="semiParSimStudies.Rdata")

#### tables for the main paper ####
load(file="semiParSimStudies.Rdata")
S.global <- 5000 # number of data sets in each simulation, for the paper will be 5000
M.global <- 10000 # number of simulations used to approximate cd's, for the paper will be 10000

library(xtable)
df1 <- rbind( 
  c( mean(s1$c80),median(s1$w80),mean(s1$c90),median(s1$w90),mean(s1$c95),median(s1$w95), sum(s1$rej)/(sum(s1$rej)+S.global*M.global) ),
  c( mean(s1$c80.b),median(s1$w80.b),mean(s1$c90.b),median(s1$w90.b),mean(s1$c95.b),median(s1$w95.b), NA ),
  c( mean(s1$c80.n),median(s1$w80.n),mean(s1$c90.n),median(s1$w90.n),mean(s1$c95.n),median(s1$w95.n), NA ),
  
  c( mean(s1.1$c80),median(s1.1$w80),mean(s1.1$c90),median(s1.1$w90),mean(s1.1$c95),median(s1.1$w95), sum(s1.1$rej)/(sum(s1.1$rej)+S.global*M.global) ),
  c( mean(s1.1$c80.b),median(s1.1$w80.b),mean(s1.1$c90.b),median(s1.1$w90.b),mean(s1.1$c95.b),median(s1.1$w95.b),NA ),
  c( mean(s1.1$c80.n),median(s1.1$w80.n),mean(s1.1$c90.n),median(s1.1$w90.n),mean(s1.1$c95.n),median(s1.1$w95.n),NA ),
  
  c( mean(s1.2$c80),median(s1.2$w80),mean(s1.2$c90),median(s1.2$w90),mean(s1.2$c95),median(s1.2$w95), sum(s1.2$rej)/(sum(s1.2$rej)+S.global*M.global) ),
  c( mean(s1.2$c80.b),median(s1.2$w80.b),mean(s1.2$c90.b),median(s1.2$w90.b),mean(s1.2$c95.b),median(s1.2$w95.b), NA ), 
  c( mean(s1.2$c80.n),median(s1.2$w80.n),mean(s1.2$c90.n),median(s1.2$w90.n),mean(s1.2$c95.n),median(s1.2$w95.n), NA ) 
  
)
colnames(df1) <- c("C% .8"," MedW .8","C% .9"," MedW .9","C% .95"," MedW .95", "P(Rej)")
rownames(df1) <- c("Case 1 (n=10)","Res. Bootstrap (n=10)","T-Interval (n=10)",
                   "Case 1 (n=30)","Res. Bootstrap (n=30)","T-Interval (n=30)",
                   "Case 1 (n=50)","Res. Bootstrap (n=50)","T-Interval (n=50)"
)
xtable(df1,digits=3,caption="Results of Simulation Study 1")

df2 <- rbind( 
  c( mean(s2$c80),median(s2$w80),mean(s2$c90),median(s2$w90),mean(s2$c95),median(s2$w95), sum(s2$rej)/(sum(s2$rej)+S.global*M.global) ),
  c( mean(s2$c80.b),median(s2$w80.b),mean(s2$c90.b),median(s2$w90.b),mean(s2$c95.b),median(s2$w95.b), NA ),
  c( mean(s2$c80.n),median(s2$w80.n),mean(s2$c90.n),median(s2$w90.n),mean(s2$c95.n),median(s2$w95.n), NA ),
  
  c( mean(s2.1$c80),median(s2.1$w80),mean(s2.1$c90),median(s2.1$w90),mean(s2.1$c95),median(s2.1$w95), sum(s2.1$rej)/(sum(s2.1$rej)+S.global*M.global) ),
  c( mean(s2.1$c80.b),median(s2.1$w80.b),mean(s2.1$c90.b),median(s2.1$w90.b),mean(s2.1$c95.b),median(s2.1$w95.b),NA ),
  c( mean(s2.1$c80.n),median(s2.1$w80.n),mean(s2.1$c90.n),median(s2.1$w90.n),mean(s2.1$c95.n),median(s2.1$w95.n),NA ),
  
  c( mean(s2.2$c80),median(s2.2$w80),mean(s2.2$c90),median(s2.2$w90),mean(s2.2$c95),median(s2.2$w95), sum(s2.2$rej)/(sum(s2.2$rej)+S.global*M.global) ),
  c( mean(s2.2$c80.b),median(s2.2$w80.b),mean(s2.2$c90.b),median(s2.2$w90.b),mean(s2.2$c95.b),median(s2.2$w95.b), NA ), 
  c( mean(s2.2$c80.n),median(s2.2$w80.n),mean(s2.2$c90.n),median(s2.2$w90.n),mean(s2.2$c95.n),median(s2.2$w95.n), NA ) 
)
colnames(df2) <- c("C% .8"," MedW .8","C% .9"," MedW .9","C% .95"," MedW .95", "P(Rej)")
rownames(df2) <- c("Case 2 (n=10)","Med. Bootstrap (n=10)","T-Interval (n=10)",
                   "Case 2 (n=30)","Med. Bootstrap (n=30)","T-Interval (n=30)",
                   "Case 2 (n=50)","Med. Bootstrap (n=50)","T-Interval (n=50)"
)
xtable(df2,digits=3,caption="Results of Simulation Study 2")

df3 <- rbind( 
  c( mean(s3$c80),median(s3$w80),mean(s3$c90),median(s3$w90),mean(s3$c95),median(s3$w95), sum(s3$rej)/(sum(s3$rej)+S.global*M.global) ),
  c( mean(s3$c80.cr),median(s3$w80.cr),mean(s3$c90.cr),median(s3$w90.cr),mean(s3$c95.cr),median(s3$w95.cr), sum(s3$rej.cr)/(sum(s3$rej.cr)+S.global*M.global) ),
  c( mean(s3$c80.b),median(s3$w80.b),mean(s3$c90.b),median(s3$w90.b),mean(s3$c95.b),median(s3$w95.b), NA ),
  c( mean(s3$c80.n),median(s3$w80.n),mean(s3$c90.n),median(s3$w90.n),mean(s3$c95.n),median(s3$w95.n), NA ),
  
  c( mean(s3.1$c80),median(s3.1$w80),mean(s3.1$c90),median(s3.1$w90),mean(s3.1$c95),median(s3.1$w95), sum(s3.1$rej)/(sum(s3.1$rej)+S.global*M.global) ),
  c( mean(s3.1$c80.cr),median(s3.1$w80.cr),mean(s3.1$c90.cr),median(s3.1$w90.cr),mean(s3.1$c95.cr),median(s3.1$w95.cr), sum(s3.1$rej.cr)/(sum(s3.1$rej.cr)+S.global*M.global)  ),
  c( mean(s3.1$c80.b),median(s3.1$w80.b),mean(s3.1$c90.b),median(s3.1$w90.b),mean(s3.1$c95.b),median(s3.1$w95.b),NA ),
  c( mean(s3.1$c80.n),median(s3.1$w80.n),mean(s3.1$c90.n),median(s3.1$w90.n),mean(s3.1$c95.n),median(s3.1$w95.n),NA ),
  
  c( mean(s3.2$c80),median(s3.2$w80),mean(s3.2$c90),median(s3.2$w90),mean(s3.2$c95),median(s3.2$w95), sum(s3.2$rej)/(sum(s3.2$rej)+S.global*M.global) ),
  c( mean(s3.2$c80.cr),median(s3.2$w80.cr),mean(s3.2$c90.cr),median(s3.2$w90.cr),mean(s3.2$c95.cr),median(s3.2$w95.cr), sum(s3.2$rej.cr)/(sum(s3.2$rej.cr)+S.global*M.global)  ), 
  c( mean(s3.2$c80.b),median(s3.2$w80.b),mean(s3.2$c90.b),median(s3.2$w90.b),mean(s3.2$c95.b),median(s3.2$w95.b), NA ), 
  c( mean(s3.2$c80.n),median(s3.2$w80.n),mean(s3.2$c90.n),median(s3.2$w90.n),mean(s3.2$c95.n),median(s3.2$w95.n), NA )

)
colnames(df3) <- c("C% .8"," MedW .8","C% .9"," MedW .9","C% .95"," MedW .95", "P(Rej)")
rownames(df3) <- c("Case 3 (n=10)","Centered Ranks (n=10)","Wild Bootstrap (n=10)","T-Interval (n=10)",
                   "Case 3 (n=11)","Centered Ranks (n=11)","Wild Bootstrap (n=11)","T-Interval (n=11)",
                   "Case 3 (n=30)","Centered Ranks (n=30)","Wild Bootstrap (n=30)","T-Interval (n=30)",
                   "Case 3 (n=31)","Centered Ranks (n=31)","Wild Bootstrap (n=31)","T-Interval (n=31)",
                   "Case 3 (n=50)","Centered Ranks (n=50)","Wild Bootstrap (n=50)","T-Interval (n=50)",
                   "Case 3 (n=51)","Centered Ranks (n=51)","Wild Bootstrap (n=51)","T-Interval (n=51)"
)
xtable(df3,digits=3,caption="Results of Simulation Study 3")



