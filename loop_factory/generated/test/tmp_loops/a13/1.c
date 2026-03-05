int main1(int g){
  int qcm, i42t, v, r;

  qcm=27;
  i42t=qcm;
  v=5;
  r=0;

  while (i42t<qcm) {
      r = i42t%5;
      if (i42t>=v) {
          v = (i42t-v)%5;
          v = v+r-v;
      }
      else {
          v += r;
      }
      i42t += 1;
      g += r;
  }

}
