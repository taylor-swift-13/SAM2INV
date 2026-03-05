int main43(int y,int l,int z){
  int p29s, eq, gl8, x3, t9, q, rx3, u;

  p29s=(z%29)+11;
  eq=4;
  gl8=p29s;
  x3=0;
  t9=0;
  q=12;
  rx3=p29s;
  u=p29s;

  while (eq<p29s) {
      x3 = x3+gl8*eq;
      gl8 = gl8 + 1;
      t9 = t9+(x3%5);
      rx3 = rx3 + x3;
      q += eq;
      u = u + x3;
  }

}
