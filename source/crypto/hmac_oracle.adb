with GNAT.SHA256; use GNAT.SHA256;
with Ada.Text_IO; use Ada.Text_IO;
procedure HMAC_Oracle
is
   OO : constant Character := Character'Val(0);
   FF : constant Character := Character'Val(16#FF#);

   -- Must match mock_key in crypto.c
   Mock_Key : String(1..32) :=
     (OO, FF, OO, FF, OO, FF, OO, FF,
      OO, FF, OO, FF, OO, FF, OO, FF,
      OO, FF, OO, FF, OO, FF, OO, FF,
      OO, FF, OO, FF, OO, FF, OO, FF);

   C : Context;
   M1 : constant String(1..32) := (others => 'A');
   M2 : constant String(1..32) := (others => 'B');
   M3 : constant String(1..32) := (others => 'C');
begin
   C := HMAC_Initial_Context (Mock_Key);
   Update (C, M1);
   Put_Line (Digest (C));

   C := HMAC_Initial_Context (Mock_Key);
   Update (C, M2);
   Put_Line (Digest (C));

   C := HMAC_Initial_Context (Mock_Key);
   Update (C, M3);
   Put_Line (Digest (C));
end HMAC_Oracle;
