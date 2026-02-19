int main1(int a,int q){
  int l, i, v, k;

  l=(q%40)+10;
  i=0;
  v=a;
  k=l;

  while (i<l) {
      v = v+3;
      i = i+5;
  }

  while (v>0) {
      i = i+1;
      i = i+i;
      v = v-1;
  }

}
