int main1(int l,int k){
  int nl, i7, o5o, c, w5, je;

  nl=0;
  i7=(k%20)+10;
  o5o=(k%15)+8;
  c=-1;
  w5=0;
  je=nl;

  while (i7>0&&o5o>0) {
      if (nl%2==0) {
          i7 -= 1;
      }
      else {
          o5o = o5o - 1;
      }
      nl += 1;
      if (k<je+1) {
          w5 = w5 + k;
      }
      c = c + 1;
      k = k+(nl%2);
      w5 = w5 + c;
      if (k<o5o+4) {
          je = je + 1;
      }
      l = je-l;
      je = je + 1;
      k = k + je;
  }

}
