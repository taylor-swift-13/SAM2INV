int main1(int a,int q){
  int l, i, v, o;

  l=42;
  i=l;
  v=q;
  o=a;

  while (i>0) {
      o = o+o;
      i = i-1;
  }

  while (o>0) {
      l = l+6;
      o = o-1;
  }

}
