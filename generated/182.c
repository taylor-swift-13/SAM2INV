int main182(int t){
  int o, np, banc, xyz;

  o=t;
  np=o;
  banc=np;
  xyz=8;

  for (; np>=2; np = np/2) {
      banc = banc*3+3;
      xyz = xyz*banc+3;
  }

}
