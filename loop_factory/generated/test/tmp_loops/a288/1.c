int main1(int a,int p){
  int l, i, v;

  l=(p%23)+12;
  i=l;
  v=-4;

  while (i>0) {
      v = v+i;
      i = i-1;
  }

  while (i<v) {
      l = l+1;
      l = l-l;
      i = i*3;
  }

}
