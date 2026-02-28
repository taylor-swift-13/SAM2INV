int main1(int m,int p){
  int z, x, v, h;

  z=p;
  x=3;
  v=z;
  h=p;

  while (1) {
      v = v+8;
      h = h+8;
      v = v+1;
      h = h-1;
      v = h-v;
      v = v+h;
  }

}
