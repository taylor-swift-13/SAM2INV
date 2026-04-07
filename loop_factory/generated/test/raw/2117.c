int main1(int l){
  int o0i, p87, u3, f, n;

  o0i=22;
  p87=0;
  u3=p87;
  f=0;
  n=o0i;

  while (p87 < o0i) {
      u3 += n;
      p87 = p87 + (f ^= 1);
      n += f;
  }

}
