int main1(int k,int n){
  int m, y, v;

  m=k;
  y=m;
  v=y;

  while (y>=1) {
      v = v+4;
      if (y<v+2) {
          v = v+v;
      }
      if (y+7<=v+m) {
          v = v+y;
      }
  }

}
