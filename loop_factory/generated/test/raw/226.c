int main1(int i){
  int hfw5, tt4, b, s, t4u;

  hfw5=i*5;
  tt4=hfw5;
  b=tt4;
  s=0;
  t4u=i;

  while (tt4-1>=0) {
      s += b;
      b += tt4;
      i = i+hfw5-tt4;
      tt4 += 1;
  }

  while (t4u<=b-1) {
      s = s + i;
      t4u = t4u + 1;
      tt4 = tt4*2;
      i = i + s;
  }

}
