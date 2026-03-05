int main1(int i){
  int j, b, q, f;

  j=(i%16)+20;
  b=0;
  q=i;
  f=0;

  while (b+2<=j) {
      f = f + 1;
      q = q+f*f*f*f;
      i = i*3+(f%6)+3;
  }

}
