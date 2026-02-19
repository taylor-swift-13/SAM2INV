int main1(int b,int p){
  int l, i, v;

  l=(p%21)+13;
  i=l;
  v=-6;

  while (i>0) {
      v = v+v;
      v = v+1;
      i = i-1;
  }

  while (l<v) {
      i = i;
      l = l+4;
  }

}
