int main1(int a,int b,int m,int p){
  int l, i, v, w;

  l=61;
  i=0;
  v=-3;
  w=-4;

  while (i<l) {
      v = v+w+w;
      v = v+1;
      w = w+1;
      if (i+2<=w+l) {
          v = v+w;
      }
      v = v+1;
      i = i+1;
  }

}
