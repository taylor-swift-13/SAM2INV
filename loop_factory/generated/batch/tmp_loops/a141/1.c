int main1(int k,int n){
  int l, c, v, p;

  l=(n%24)+9;
  c=1;
  v=l;
  p=n;

  while (c*3<=l) {
      v = v+1;
      p = p-1;
      v = v+c;
  }

}
