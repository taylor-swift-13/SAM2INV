int main1(int p,int q){
  int l, i, v, s;

  l=(q%28)+10;
  i=0;
  v=-4;
  s=q;

  while (i<l) {
      v = v+4;
      s = s+3;
      i = i+3;
  }

  while (v<l) {
      v = v+1;
  }

}
