int main1(int b,int n,int k){
  int i0a, kx;

  i0a=3;
  kx=(n%20)+5;

  while (1) {
      if (!(kx>0)) {
          break;
      }
      kx = kx - 1;
      b = b + 3;
      n += i0a;
      k += 1;
  }

}
