int main1(){
  int veg, nj, e7z, vc, r, l, www, xl, ng, k4;

  veg=(1%13)+20;
  nj=0;
  e7z=nj;
  vc=0;
  r=veg;
  l=veg;
  www=0;
  xl=veg;
  ng=0;
  k4=0;

  while (nj<veg) {
      if (r==veg+1) {
          e7z = e7z + 3;
          vc = vc + 3;
      }
      else {
          e7z += 2;
          vc += 2;
      }
      if (r==veg) {
          e7z += 1;
          r = r + 1;
      }
      ng += e7z;
      k4 = k4 + 1;
      l = l + 1;
      xl = xl + 3;
      www = www + 1;
      nj = veg;
  }

}
