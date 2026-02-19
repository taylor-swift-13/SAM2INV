int main1(int a,int m){
  int l, i, v;

  l=(a%31)+15;
  i=l;
  v=i;

  while (i>0) {
      v = v-v;
      i = i-1;
  }

  while (v<i) {
      l = l+l;
      l = l+v;
      v = v+1;
  }

}
