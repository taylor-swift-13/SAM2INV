int main1(int m,int p){
  int l, i, v, f;

  l=18;
  i=l;
  v=-5;
  f=-2;

  while (i>0) {
      v = v+1;
      f = f-1;
  }

  while (f<v) {
      i = i+6;
      i = i+f;
      f = f+4;
  }

}
