int main1(int b,int p){
  int l, i, v;

  l=(p%16)+10;
  i=0;
  v=-2;

  while (i<l) {
      v = v+i;
      v = v+v;
      i = i+1;
  }

  while (l<v) {
      i = i+1;
      l = l+4;
  }

}
