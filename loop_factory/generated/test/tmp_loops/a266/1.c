int main1(int a,int b){
  int l, i, v, f;

  l=a;
  i=0;
  v=l;
  f=-8;

  while (i<l) {
      v = v+f+f;
      i = i+1;
  }

  while (v<l) {
      i = i-i;
      v = v+1;
  }

}
