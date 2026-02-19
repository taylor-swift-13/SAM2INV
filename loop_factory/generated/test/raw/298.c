int main1(int b,int n){
  int l, i, v;

  l=(n%13)+12;
  i=0;
  v=-3;

  while (i<l) {
      v = i-i;
      i = i+1;
  }

  while (v<l) {
      i = i-i;
      i = i+5;
      v = v*2;
  }

}
