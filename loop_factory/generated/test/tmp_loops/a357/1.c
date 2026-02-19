int main1(int a,int n){
  int l, i, v;

  l=(a%13)+5;
  i=0;
  v=l;

  while (i<l) {
      v = v-v;
      i = i+3;
  }

  while (l<i) {
      l = l+1;
  }

}
