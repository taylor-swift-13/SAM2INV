int main1(int a,int q){
  int l, i, v;

  l=(a%15)+12;
  i=0;
  v=8;

  while (i<l) {
      v = v+v;
      i = i+1;
  }

  while (v<i) {
      v = v+1;
  }

}
