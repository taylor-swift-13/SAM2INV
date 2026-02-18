int main1(int n,int q){
  int l, i, v;

  l=21;
  i=0;
  v=q;

  while (i<l) {
      if ((i%9)==0) {
          v = v+v;
      }
      i = i+1;
  }

}
