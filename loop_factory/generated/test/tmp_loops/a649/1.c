int main1(int a,int p){
  int l, i, v, j;

  l=(a%18)+19;
  i=0;
  v=p;
  j=l;

  while (i<l) {
      v = v+2;
      i = i+1;
  }

  while (v>0) {
      v = v/2;
  }

}
