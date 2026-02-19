int main1(int a,int m){
  int l, i, v;

  l=(a%6)+17;
  i=l;
  v=i;

  while (i>0) {
      v = v+i;
      v = v-v;
      i = i-1;
  }

  while (i<l) {
      i = i+1;
  }

}
