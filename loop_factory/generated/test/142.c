int main142(int b,int k,int n){
  int l, d, z, o, i;

  l=k+4;
  d=0;
  z=-8;
  o=n;
  i=b;

  while (d<=l-4) {
      z = z+1;
      o = o+z;
      if (d+6<=i+l) {
          o = o+z;
      }
      d = d+4;
  }

  while (o<=l-1) {
      if (d+2<=l) {
          d = d+2;
      }
      else {
          d = l;
      }
  }

  while (1) {
      i = i*4+1;
      d = d*i+1;
      i = i+d;
      d = d+o;
  }


  /*@ assert \false; */
}
