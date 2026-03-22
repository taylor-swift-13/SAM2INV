int main1(int k,int f){
  int luv, qy6, g1, qoi, l, dx, pz;

  luv=53;
  qy6=0;
  g1=0;
  qoi=0;
  l=0;
  dx=4;
  pz=0;

  for (; qy6<=luv-1; qy6 = qy6 + 1) {
      if (qy6%3==0) {
          if (g1>0) {
              g1 = g1 - 1;
              l = l + 1;
          }
      }
      else {
          if (g1<dx) {
              g1 += 1;
              qoi += 1;
          }
      }
      pz = pz + 1;
  }

}
