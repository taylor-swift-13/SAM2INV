int main169(int b,int k,int m){
  int i, r, v, l, y;

  i=(k%14)+6;
  r=i;
  v=-5;
  l=m;
  y=5;

  while (r-2>=0) {
      if (v+6<=i) {
          v = v+6;
      }
      else {
          v = i;
      }
      v = v+l;
      l = l+y;
  }

  while (y!=0&&v!=0) {
      if (y>v) {
          y = y-v;
      }
      else {
          v = v-y;
      }
  }

  while (r+1<=y) {
      i = l;
      l = l+3;
      l = l+r;
      i = i*i;
      i = i+l*i;
  }


  /*@ assert r+1 > y; */
}
