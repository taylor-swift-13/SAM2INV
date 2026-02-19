int main1(int m,int q){
  int l, i, v, o;

  l=(m%21)+16;
  i=0;
  v=i;
  o=i;

  while (i<l) {
      v = v+1;
      o = o+1;
  }

  while (v<l) {
      o = o-o;
      o = o+v;
      v = v+1;
  }

}
