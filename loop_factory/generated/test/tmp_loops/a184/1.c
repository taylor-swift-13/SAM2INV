int main1(int b,int p){
  int l, i, v;

  l=p+5;
  i=1;
  v=p;

  while (i<l) {
      v = v+5;
      v = v+v;
      i = i*3;
  }

  while (i<v) {
      l = l-l;
      i = i+3;
  }

}
