int main1(int n,int q){
  int l, i, v;

  l=(n%17)+5;
  i=0;
  v=-8;

  while (i<l) {
      v = v+6;
      v = v+1;
      i = i+5;
  }

  while (v<l) {
      i = i+1;
      v = v+1;
  }

}
