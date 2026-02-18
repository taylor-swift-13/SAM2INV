int main1(int k,int m){
  int l, i, v;

  l=(k%14)+7;
  i=0;
  v=l;

  while (i<l) {
      if (i+6<=v+l) {
          v = v*v;
      }
      i = i+1;
  }

}
