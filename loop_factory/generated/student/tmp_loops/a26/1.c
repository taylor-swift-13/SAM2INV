int main1(int b,int n){
  int l, z, c;

  l=(n%26)+18;
  z=1;
  c=l;

  while (z*3<=l) {
      c = c+2;
      c = c*c+c;
  }

}
