int main1(int n,int p){
  int l, i, v, o;

  l=n;
  i=0;
  v=i;
  o=l;

  while (i<l) {
      if (v+2<=l) {
          v = v+2;
      }
      else {
          v = l;
      }
      v = v+o;
      o = o+o;
  }

}
