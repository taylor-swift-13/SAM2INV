int main1(int a,int p){
  int l, i, v;

  l=(a%33)+9;
  i=0;
  v=l;

  while (i<l) {
      v = v+1;
      i = i+1;
  }

  while (i>0) {
      v = v+i;
      i = i-1;
  }

}
