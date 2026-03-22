int main1(){
  int mm, xt7v, qv, vgg, d0;

  mm=1;
  xt7v=mm;
  qv=0;
  vgg=mm;
  d0=0;

  while (d0<=mm) {
      xt7v = xt7v + qv;
      qv += vgg;
      xt7v = xt7v*3;
      d0++;
      qv = qv/3;
      vgg += 4;
  }

}
