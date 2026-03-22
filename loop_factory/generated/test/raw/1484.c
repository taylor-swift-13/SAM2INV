int main1(int w){
  int f2ul, v, p2a;

  f2ul=(w%27)+17;
  v=0;
  p2a=5;

  while (v > 0 && f2ul > 0) {
      v -= 1;
      f2ul = f2ul - 1;
      p2a += v;
  }

}
