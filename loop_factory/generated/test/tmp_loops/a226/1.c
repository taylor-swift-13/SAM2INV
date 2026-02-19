int main1(int a,int q){
  int l, i, v;

  l=(a%12)+8;
  i=0;
  v=-4;

  while (i<l) {
      v = v+i;
      i = i+1;
  }

  while (v<i) {
      v = v+5;
  }

}
