int main1(int p,int q){
  int d, y, v, i;

  d=p;
  y=2;
  v=d;
  i=q;

  while (y<d) {
      if (y<d/2) {
          v = v+i;
      }
      else {
          v = v*i;
      }
      v = v*3+4;
  }

}
