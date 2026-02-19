int main1(int a,int b){
  int l, i, v;

  l=(b%10)+20;
  i=0;
  v=i;

  while (i<l) {
      v = v-v;
      i = i+1;
  }

  while (l>0) {
      i = i+l;
      l = l-1;
  }

}
