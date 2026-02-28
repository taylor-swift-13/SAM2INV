int main1(int a,int k){
  int i, o, b, j;

  i=(k%30)+18;
  o=0;
  b=4;
  j=-8;

  while (1) {
      b = b+1;
      j = j+1;
      b = b+1;
      j = j-1;
      b = j-b;
      j = j+o;
      j = b-j;
  }

}
