int main1(int k,int m){
  int v, i, c, o;

  v=k+23;
  i=v;
  c=0;
  o=v;

  while (c!=0&&o!=0) {
      if (c>o) {
          c = c-o;
      }
      else {
          o = o-c;
      }
      c = c*3;
      o = o/3;
      c = o*o;
      o = o*o+c;
      c = c*o;
  }

}
