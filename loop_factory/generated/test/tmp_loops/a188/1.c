int main1(int b,int p){
  int l, i, v;

  l=(p%34)+11;
  i=0;
  v=6;

  while (i<l) {
      v = v+v;
      i = i+1;
  }

  while (l<i) {
      v = v+l;
      v = v+v;
      l = l+1;
  }

}
