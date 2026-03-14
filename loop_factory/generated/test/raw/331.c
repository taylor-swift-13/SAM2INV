int main1(){
  int ii, d, xiyz, n;

  ii=1*3;
  d=0;
  xiyz=-2;
  n=8;

  while (xiyz<ii) {
      xiyz = xiyz + 1;
      d++;
      n = n+(d%6);
      n = n*4+2;
  }

  while (d>5) {
      xiyz = xiyz+ii*d;
      ii += xiyz;
      d = 5;
  }

}
