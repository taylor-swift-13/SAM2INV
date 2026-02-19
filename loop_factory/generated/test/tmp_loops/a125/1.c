int main1(int a,int p){
  int l, i, v, o;

  l=35;
  i=0;
  v=i;
  o=l;

  while (i<l) {
      o = o+o;
      o = o+v;
      i = i+5;
  }

  while (v<i) {
      o = o+o;
      v = v+2;
  }

}
