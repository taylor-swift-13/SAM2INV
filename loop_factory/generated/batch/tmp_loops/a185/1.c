int main1(int a,int p){
  int n, d, z;

  n=(p%39)+19;
  d=n;
  z=3;

  while (d>0) {
      z = z*z+z;
      d = d-1;
  }

}
