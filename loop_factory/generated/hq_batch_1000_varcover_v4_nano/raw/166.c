int main1(int a,int b,int p){
  int l, i, v, y;

  l=57;
  i=0;
  v=a;
  y=b;

  while (i<l) {
      v = v+1;
      y = y-1;
      v = v+y;
      v = v+i;
      i = i+1;
  }

}
