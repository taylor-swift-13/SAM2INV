int main1(int n){
  int oy, j, gb, cfo, ez;

  oy=(n%12)+12;
  j=0;
  gb=0;
  cfo=0;
  ez=0;

  while (j < oy) {
      ez = ez + (n % (j+1));
      cfo = cfo + (n / (j+1));
      gb = gb + (n / (j+1)) - (n % (j+1));
      j++;
  }

}
