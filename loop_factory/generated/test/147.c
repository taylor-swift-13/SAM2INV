int main147(int b,int k,int p){
  int o, i, v;

  o=k;
  i=0;
  v=k;

  while (i<=o-1) {
      v = v+2;
      v = v+1;
      if ((i%7)==0) {
          v = v+1;
      }
  }

  while (i>=1) {
      o = o+4;
      o = o%7;
      if (b*b<=v+2) {
          o = o+o;
      }
      o = o*o+o;
  }

  while (o>0) {
      i = i+4;
      i = i*i+i;
  }

}
