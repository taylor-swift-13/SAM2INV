int main1(){
  int ar, yr, qn, w, fu, gg, l;

  ar=1+4;
  yr=ar;
  qn=0;
  w=0;
  fu=0;
  gg=(1%18)+5;
  l=yr;

  while (gg>0) {
      qn = qn+1*1;
      fu = fu+1*1;
      w = w+1*1;
      gg = gg - 1;
      l = l + w;
  }

  while (fu>qn) {
      fu = fu - qn;
      yr = yr+gg-ar;
      qn++;
      l = (2)+(l);
      w += 1;
  }

}
