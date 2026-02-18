int main1(int a,int k,int m,int p){
  int l, i, v;

  l=(a%34)+5;
  i=0;
  v=m;

  while (i<l) {
      if ((i%8)==0) {
          v = v+i;
      }
      i = i+1;
  }

}
