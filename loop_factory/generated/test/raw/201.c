int main1(int k,int m,int n,int p){
  int l, i, v;

  l=59;
  i=0;
  v=k;

  while (i<l) {
      if ((i%9)==0) {
          v = v+3;
      }
      v = v+v;
      v = v-v;
      i = i+1;
  }

}
