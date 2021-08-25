DROP PROCEDURE IF EXISTS Query5;
DELIMITER //
CREATE PROCEDURE Query5(in kcaller varchar(250), in krole varchar(250))
BEGIN
DECLARE _rollback int DEFAULT 0;
DECLARE EXIT HANDLER FOR SQLEXCEPTION
BEGIN
  SET _rollback = 1;
  GET STACKED DIAGNOSTICS CONDITION 1 
    @p1 = RETURNED_SQLSTATE, @p2 = MESSAGE_TEXT;
  SELECT @p1, @p2;
  ROLLBACK;
END;
START TRANSACTION;
/* If the user is role lecturer and is the oldest i.e. 
 Lecturer.allInstances()->forAll(l|l.age <= caller.age) */
IF (krole = 'Lecturer' AND
  ((SELECT MAX(age) FROM Lecturer)
    = (SELECT age FROM Lecturer WHERE Lecturer_id = kcaller)))
THEN 
  DROP TEMPORARY TABLE IF EXISTS TEMP1;
  CREATE TEMPORARY TABLE TEMP1 AS (
    SELECT * FROM Student
    WHERE age > 18
  );
ELSE 
  DROP TEMPORARY TABLE IF EXISTS TEMP1;
  CREATE TEMPORARY TABLE TEMP1 AS (
    SELECT * FROM Student
    WHERE CASE auth_READ_Student_age(kcaller, krole, Student_id)
    WHEN 1 THEN age ELSE throw_error() END > 18
  );
END IF;

DROP TEMPORARY TABLE IF EXISTS TEMP2;
CREATE TEMPORARY TABLE TEMP2 AS (
  SELECT Student_id AS Student_id FROM TEMP1
);

IF _rollback = 0
THEN SELECT COUNT(*) from TEMP2;
END IF;
END //
DELIMITER ;