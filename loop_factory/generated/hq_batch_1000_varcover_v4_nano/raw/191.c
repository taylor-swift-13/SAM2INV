int main1(int b,int m,int q){
  int l, i, v;

  l=(m%6)+13;
  i=l;
  v=i;

  while (i>0) {
      v = v+v;
      v = v+v;
      v = v+1;
      v = v+v;
      v = v-v;
      i = i-1;
  }

}
