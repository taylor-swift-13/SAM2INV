int main1(int k,int p){
  int d, i, v;

  d=p+3;
  i=1;
  v=d;

  while (i<d) {
      v = v*v+v;
      v = v+i;
      i = i*2;
  }

}
